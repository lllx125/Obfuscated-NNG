import torch
import gc
import re
import json
from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig
from typing import Dict, List, Any, Optional, Tuple

# ============================================================================
# ROBUST PARSING
# ============================================================================

def extract_json_from_response(text: str) -> Optional[Dict[str, Any]]:
    """
    Robustly extracts and fixes JSON from LLM responses.
    Handles ```json blocks, literal newlines inside strings, and conversational filler.
    """

    def sanitize_json_string(match):
        """Helper to escape control characters inside found JSON strings."""
        content = match.group(0)
        content = content.replace('\n', '\\n')
        content = content.replace('\r', '')
        content = content.replace('\t', '\\t')
        return content

    def robust_parse(candidate_text):
        """Attempts to parse JSON, applying repairs if standard parsing fails."""
        try:
            return json.loads(candidate_text)
        except json.JSONDecodeError:
            # Repair Strategy: Escape newlines inside string values
            string_pattern = r'"(?:\\.|[^"\\])*"'
            repaired_text = re.sub(string_pattern, sanitize_json_string, candidate_text)
            try:
                return json.loads(repaired_text)
            except json.JSONDecodeError:
                return None

    # STRATEGY 1: Extract from Code Blocks (Highest Confidence)
    code_block_pattern = r'```(?:json)?\s*(\{.*?\})\s*```'
    matches = re.findall(code_block_pattern, text, re.DOTALL)
    for match in matches:
        result = robust_parse(match)
        if result and "draft" in result and "code" in result:
            return result

    # STRATEGY 2: Extract Outermost Braces (Fallback)
    brace_matches = re.findall(r'\{.*\}', text, re.DOTALL)
    if brace_matches:
        candidate = brace_matches[-1]
        result = robust_parse(candidate)
        if result and "draft" in result and "code" in result:
            return result

    return None

def validate_schema(data: Any) -> bool:
    """Checks if the JSON has exactly the required fields."""
    if not isinstance(data, dict): return False
    return "draft" in data and "code" in data

def extract_lean_code_from_response(text: str) -> Dict[str, str]:
    """
    Extracts Lean code from response for deepseek-prover, goedel-prover, deepseek-r1 models.
    Identifies the final block of code wrapped with ```lean```, ```lean4```, or just ```.
    If theorem keyword is found, removes everything from "theorem" to "by" (inclusive).
    Returns dict with 'draft' and 'code' fields.
    """
    # Try to find Lean code blocks with different markers
    # Priority: ```lean4, ```lean, then unmarked ```
    patterns = [
        r'```lean4\s*\n(.*?)\n\s*```',
        r'```lean\s*\n(.*?)\n\s*```',
        r'```\s*\n(.*?)\n\s*```'
    ]

    code_block = None
    full_match = None

    for pattern in patterns:
        matches = re.findall(pattern, text, re.DOTALL)
        if matches:
            # Get the last code block
            code_block = matches[-1]
            # Also get the full match to remove it from draft
            full_matches = re.finditer(pattern, text, re.DOTALL)
            for m in full_matches:
                full_match = m
            break

    if code_block:
        # Remove the code block from the original text to get draft
        if full_match:
            draft = text[:full_match.start()] + text[full_match.end():]
            draft = draft.strip()
        else:
            draft = text.strip()

        return {
            "draft": draft,
            "code": code_block.strip()
        }
    else:
        # No code block found, use "sorry" for code
        return {
            "draft": text.strip(),
            "code": "sorry"
        }

# ============================================================================
# MODEL INTERFACE
# ============================================================================

class ModelInterface:
    """Singleton-style interface to handle model loading and generation."""

    def __init__(self, llm_name: str, max_retry: int = 3):
        self.llm_name = llm_name.lower()
        self.max_retry = max_retry
        self.model = None
        self.tokenizer = None
        self._load_model()

    def _load_model(self):
        """Loads the specific model based on the name."""
        if self.model is not None:
            return

        print(f"[*] Initializing Model: {self.llm_name}...")
        
        if self.llm_name == "deepseek-prover-v2":
            self._load_local_prover("deepseek-ai/DeepSeek-Prover-V2-7B")
        elif self.llm_name == "goedel-prover-v2":
            self._load_local_prover("Goedel-LM/Goedel-Prover-V2-8B")
        elif self.llm_name in ["deepseek-r1", "gemini-2.5", "gpt-4o-mini", "gemini-1.5-flash"]:
            print(f"[!] API Model selected: {self.llm_name}. (Placeholder initialized)")
        else:
            raise ValueError(f"Unknown LLM: {self.llm_name}")

    def _load_local_prover(self, model_id: str):
        """Loads local HuggingFace models with 4-bit quantization."""
        torch.manual_seed(30) # consistent seeding
        
        quantization_config = BitsAndBytesConfig(
            load_in_4bit=True,
            bnb_4bit_quant_type="nf4",
            bnb_4bit_compute_dtype=torch.bfloat16,
            bnb_4bit_use_double_quant=True
        )

        self.tokenizer = AutoTokenizer.from_pretrained(model_id, trust_remote_code=True)
        # Fix: Explicitly tell the model to use EOS as PAD
        self.tokenizer.pad_token = self.tokenizer.eos_token
        self.tokenizer.pad_token_id = self.tokenizer.eos_token_id

        self.model = AutoModelForCausalLM.from_pretrained(
            model_id,
            quantization_config=quantization_config,
            device_map="auto",
            trust_remote_code=True
        )
        print(f"[+] Model {model_id} loaded successfully.")

    def generate(self, messages: List[Dict[str, str]]) -> Dict[str, str]:
        """
        Routes the generation request to the correct backend with retry logic.
        Returns a dictionary with 'draft' and 'code' fields.
        """
        messages = self._append_llm_specific_instructions(messages)

        valid_response = None

        # Retry Loop
        for attempt in range(self.max_retry + 1):
            raw_output = self._generate_raw(messages)
            processed_output = self._process_output(raw_output)

            if validate_schema(processed_output):
                valid_response = processed_output
                break

        # Default failure object if retries exhausted
        if not valid_response:
            valid_response = {"draft": "failed", "code": "sorry"}

        return valid_response

    def _generate_raw(self, messages: List[Dict[str, str]]) -> str:
        """
        Routes the generation request to the correct backend (Local vs API).
        Returns raw string output.
        """
        if self.llm_name in ["deepseek-prover-v2", "goedel-prover-v2"]:
            return self._generate_local(messages)
        else:
            return self._generate_api(messages)

    def _process_output(self, raw_output: str) -> Dict[str, str]:
        """
        Process the raw output based on the model type.
        Returns a dictionary with 'draft' and 'code' fields.
        """
        # For deepseek-prover, goedel-prover, deepseek-r1: extract Lean code blocks
        if self.llm_name in ["deepseek-prover-v2", "goedel-prover-v2", "deepseek-r1"]:
            return extract_lean_code_from_response(raw_output)
        else:
            # For other models: extract JSON
            result = extract_json_from_response(raw_output)
            if result:
                return result
            else:
                # If extraction fails, return raw output as draft with sorry
                return {"draft": raw_output, "code": "sorry"}

    def _generate_local(self, messages: List[Dict[str, str]]) -> str:
        """
        Generates response using local GPU model with strict memory cleanup.
        """
        # 1. Prepare Inputs
        inputs = self.tokenizer.apply_chat_template(
            messages, 
            tokenize=True, 
            add_generation_prompt=True, 
            return_tensors="pt"
        ).to(self.model.device)

        # Initialize variables to ensure they exist for the finally block
        outputs = None
        
        try:
            # 2. Generate
            outputs = self.model.generate(
                inputs, 
                max_new_tokens=8192, 
                pad_token_id=self.tokenizer.eos_token_id
            )
            
            # 3. Decode
            # Only decode the new tokens (skipping the input prompt)
            generated_ids = outputs[0][inputs.shape[1]:]
            response = self.tokenizer.decode(generated_ids, skip_special_tokens=True)
            return response

        except Exception as e:
            # If generation fails (e.g. OOM), we still want to clean up
            print(f"[!] Local generation error: {e}")
            return '{"draft": "failed", "code": "sorry"}'

        finally:
            # 4. Aggressive Memory Cleanup
            # Delete large tensors
            del inputs
            if outputs is not None:
                del outputs
            
            # Force Python Garbage Collection
            gc.collect()
            
            # Clear PyTorch CUDA Cache (The most important step for avoiding OOM)
            if torch.cuda.is_available():
                torch.cuda.empty_cache()

    def _generate_api(self, messages: List[Dict[str, str]]) -> str:
        """Placeholder for API calls."""
        # TODO: Implement actual API calls here (OpenAI, VertexAI, etc.)
        # return call_api(self.llm_name, messages)
        return '{"draft": "API not implemented", "code": "sorry"}'
    
    def _append_llm_specific_instructions(self, messages: List[Dict[str, str]]) -> List[Dict[str, str]]:
        """
        Appends model-specific instructions to the messages.
        For deepseek-prover, goedel-prover, deepseek-r1: adds COT instruction to user role.
        For other models: adds JSON schema to system role.
        """
        cot_instruction = "Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies. The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof."

        json_schema = """### CONSTRAINTS
- **Goal:** Produce a complete, formally verifiable Lean 4 proof for the given theorem.
- **Output:** Your entire response must be a single, raw JSON object. Do NOT wrap the JSON object in markdown blocks (e.g., ```json or ```lean).
- **SCHEMA:** The JSON object MUST contain exactly two fields: "draft" and "code".
  * **"draft" (string):** Your detailed, natural language proof plan and step-by-step reasoning.
  * **"code" (string):** The final, executable Lean 4 tactic code (everything after `:= by`).

  Example format:
  {{
    "draft": "The proof plan goes here. I will use induction on 'n'...",
    "code": "induction n with d hd\\nrw [adXfkzΚro]"
  }}
"""

        if self.llm_name in ["deepseek-prover-v2", "goedel-prover-v2", "deepseek-r1"]:
            # Add COT instruction to user role (index 1)
            messages[1]["content"] += "\n\n### Instructions:\n" + cot_instruction
        else:
            # Add JSON schema to system role (index 0)
            messages[0]["content"] += "\n\n" + json_schema
        return messages