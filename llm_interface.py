import torch
import gc
import os
import psutil
from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig
from parse_output import extract_lean_code_from_response, extract_json_from_response, validate_schema
from typing import Dict, List, Any, Optional
from openai import OpenAI
from google import genai 
from google.genai import types

# ============================================================================
# CONFIGURATION
# ============================================================================

# STRATEGY: Try 8k. If OOM, auto-drop to 4k, then 2k.
MAX_TOKENS = 8192
TOKEN_TIERS = [8192, 4096, 2048]

MAX_INPUT_LENGTH = 16000 

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
        self.using_flash_attention = False 
        self._load_model()

    def _load_model(self):
        if self.model is not None: return

        print(f"[*] Initializing Model: {self.llm_name}")
        
        if self.llm_name == "deepseek-prover-v2":
            self._load_local_prover("deepseek-ai/DeepSeek-Prover-V2-7B")
        elif self.llm_name == "goedel-prover-v2":
            self._load_local_prover("Goedel-LM/Goedel-Prover-V2-8B")
        elif self.llm_name in ["deepseek-r1", "gemini-pro", "gpt-4o", "gemini-flash"]:
            print(f"[!] API Model selected: {self.llm_name}.")
        else:
            raise ValueError(f"Unknown LLM: {self.llm_name}")
    
    def generate(self, messages: List[Dict[str, str]]) -> Dict[str, str]:
        # Pre-flight check
        if not self._maintain_memory_health():
            return {"draft": "OOM PREVENTED", "code": "sorry"}

        self._append_llm_specific_instructions(messages)

        valid_response = None
        
        for attempt in range(self.max_retry + 1):
            raw_output = self._generate_raw(messages)
            processed_output = self._process_output(raw_output)

            # Crash signal handling
            if processed_output.get("draft") in ["OOM crash", "OOM PREVENTED", "OOM_SIGNAL"]:
                return processed_output

            if validate_schema(processed_output):
                valid_response = processed_output
                break

        if not valid_response:
            valid_response = {"draft": "failed", "code": "sorry"}

        return valid_response

    def _load_local_prover(self, model_id: str):
        torch.manual_seed(30)

        quantization_config = BitsAndBytesConfig(
            load_in_4bit=True,
            bnb_4bit_quant_type="nf4",
            bnb_4bit_compute_dtype=torch.bfloat16,
            bnb_4bit_use_double_quant=True
        )

        self.tokenizer = AutoTokenizer.from_pretrained(model_id, trust_remote_code=True)
        self.tokenizer.pad_token = self.tokenizer.eos_token
        self.tokenizer.pad_token_id = self.tokenizer.eos_token_id

        print(f"[+] Loading {model_id} with SDPA ...")
        self.model = AutoModelForCausalLM.from_pretrained(
            model_id,
            quantization_config=quantization_config,
            device_map="auto",
            trust_remote_code=True,
            attn_implementation="sdpa"
        )
        self.using_flash_attention = True # Keep True to enable KV cache logic
        print(f"[✓] SDPA active - memory efficient mode")
        print(f"[+] Model loaded")

    def _force_cleanup(self):
        """Forces full garbage collection and VRAM flush."""
        if torch.cuda.is_available():
            torch.cuda.synchronize()
        gc.collect()
        if torch.cuda.is_available():
            torch.cuda.empty_cache()

    def _maintain_memory_health(self) -> bool:
        """
        Smart Cleanup: Keeps VRAM usage safe.
        Eliminates the 'Grey Zone' where memory is low but not critical.
        """
        if not torch.cuda.is_available(): return True

        # Check VRAM directly from driver
        free_mem, total_mem = torch.cuda.mem_get_info(0)
        free_gb = free_mem / (1024**3)
        
        # LOGIC: 
        # If > 3.0 GB free: We are safe. Speed mode.
        # If < 3.0 GB free: We are in the Danger Zone. CLEAN IMMEDIATELY.
        if free_gb > 3.0:
            return True

        # If we are here, we are in the Grey Zone (<3GB). Force cleanup now.
        print(f"    [⚠️] VRAM Buffer Low ({free_gb:.1f}GB free). Performing proactive cleanup...")
        self._force_cleanup()
        
        # Verify result
        free_mem, _ = torch.cuda.mem_get_info(0)
        free_gb_after = free_mem / (1024**3)
        
        # If still critical after cleanup (< 1GB), then we abort.
        if free_gb_after < 1.0: 
            print(f"    [⛔] Critical VRAM ({free_gb_after:.1f}GB). Aborting to prevent crash.")
            return False

        # Check System RAM as a secondary guard
        sys_mem = psutil.virtual_memory()
        if sys_mem.percent > 90:
            print(f"    [⛔] System RAM Critical: {sys_mem.percent}%. Aborting.")
            return False

        return True

    def unload_model(self):
        if self.model:
            print(f"[-] Unloading model {self.llm_name}...")
            del self.model
            del self.tokenizer
            self.model = None
            self.tokenizer = None
            self._force_cleanup()

    def _generate_raw(self, messages: List[Dict[str, str]]) -> str:
        if self.llm_name in ["deepseek-prover-v2", "goedel-prover-v2"]:
            return self._generate_local(messages)
        else:
            return self._generate_api(messages)

    def _process_output(self, raw_output: str) -> Dict[str, str]:
        if raw_output in ["OOM_SIGNAL", "OOM_PREVENTED"]:
            return {"draft": "OOM crash", "code": "sorry"}

        if self.llm_name in ["deepseek-prover-v2", "goedel-prover-v2", "deepseek-r1"]:
            return extract_lean_code_from_response(raw_output)
        else:
            result = extract_json_from_response(raw_output)
            return result if result else {"draft": raw_output, "code": "sorry"}

    @torch.inference_mode()
    def _generate_local(self, messages: List[Dict[str, str]]) -> str:
        
        # 1. Smart Memory Check (Fast)
        self._maintain_memory_health()

        inputs = None
        outputs = None
        generated_ids = None

        try:
            # STEP 1: Pre-validate input length
            estimated_tokens = sum(len(msg["content"]) // 3.5 for msg in messages) # 3.5 chars/token estimate
            
            # Truncate if insanely long to avoid immediate crash
            if estimated_tokens > MAX_INPUT_LENGTH:
                if len(messages) > 1:
                    max_chars = int(MAX_INPUT_LENGTH * 3.5)
                    messages[1]["content"] = messages[1]["content"][:max_chars]

            inputs = self.tokenizer.apply_chat_template(
                messages, tokenize=True, add_generation_prompt=True, return_tensors="pt"
            ).to(self.model.device)

            input_len = inputs.shape[1]

            # STEP 2: Try tiers (8192 -> 4096 -> 2048)
            for attempt, max_tokens in enumerate(TOKEN_TIERS):
                
                # OPTIMIZATION: Don't even try 8192 if we are already almost full
                # If asking for >4k tokens but have <4.5GB free, skip 8k tier to save time.
                if max_tokens > 4096:
                    free_mem, _ = torch.cuda.mem_get_info(0)
                    if (free_mem / 1024**3) < 4.5:
                        continue # Skip to 4096 tier immediately

                try:
                    # FORCE CACHE = TRUE for speed
                    outputs = self.model.generate(
                        inputs,
                        max_new_tokens=max_tokens,
                        pad_token_id=self.tokenizer.eos_token_id,
                        use_cache=True, 
                        do_sample=False
                    )

                    generated_ids = outputs[0][input_len:].clone()
                    response = self.tokenizer.decode(generated_ids, skip_special_tokens=True)
                    return response # Success

                except torch.cuda.OutOfMemoryError:
                    print(f"    [⚠️] OOM at {max_tokens}. Cleaning...")
                    
                    # Local variable cleanup is critical here
                    if 'outputs' in locals(): del outputs
                    if 'generated_ids' in locals(): del generated_ids
                    outputs = None
                    generated_ids = None
                    
                    self._force_cleanup()
                    
                    # If this was the last tier, give up
                    if attempt == len(TOKEN_TIERS) - 1:
                        raise

        except torch.cuda.OutOfMemoryError:
            print("    [💥] GPU OOM DETECTED! All tiers failed.")
            return "OOM_SIGNAL"

        except Exception as e:
            print(f"    [!] Gen error: {e}")
            return '{"draft": "failed", "code": "sorry"}'

        finally:
            # Final cleanup only if variables exist
            try:
                if generated_ids is not None: del generated_ids
                if outputs is not None: del outputs
                if inputs is not None: del inputs
            except:
                pass

    def _generate_api(self, messages: List[Dict[str, str]]) -> str:
        """
        Handles API calls for OpenAI, DeepSeek, and Google Gemini.
        """
        api_key = None
        
        # --- 1. Model Mapping ---
        # Maps your internal names to the actual API model strings
        model_map = {
            "deepseek-r1": "deepseek-reasoner",
            "gpt-4o": "gpt-4o-mini",
            "gemini-flash": "gemini-2.5-flash",
            "gemini-pro": "gemini-2.5-pro", # Assuming you want the Pro model for '2.5', or change to specific ID
        }
        
        target_model = model_map[self.llm_name]

        try:
            # =================================================================
            # DEEPSEEK & OPENAI (OpenAI-Compatible APIs)
            # =================================================================
            if target_model in ["deepseek-reasoner", "gpt-4o-mini"]:
                client = None
                
                if target_model == "deepseek-reasoner":
                    api_key = os.getenv("DEEPSEEK_API_KEY")
                    base_url = "https://api.deepseek.com"
                    client = OpenAI(api_key=api_key, base_url=base_url)
                else:
                    api_key = os.getenv("OPENAI_API_KEY")
                    client = OpenAI(api_key=api_key)

                if not api_key:
                    return '{"draft": "Missing API Key", "code": "sorry"}'

                # Prepare arguments
                kwargs = {
                    "model": target_model,
                    "messages": messages,
                    "max_tokens": MAX_TOKENS,
                    "stream": False
                }
                
                is_deepseek = (target_model == "deepseek-reasoner")

                # strict JSON mode for GPT-4o
                if not is_deepseek:
                    kwargs["response_format"] = {"type": "json_object"}
                    kwargs["temperature"] = 0.2
                else:
                    # DeepSeek R1 (Reasoner) specific
                    # We don't force response_format="json_object" here as it can sometimes 
                    # conflict with the reasoning block output structure.
                    # We rely on the prompt + low temperature.
                    kwargs["temperature"] = 0.6 # R1 recommends slightly higher temp for reasoning

                response = client.chat.completions.create(**kwargs)
                
                return response.choices[0].message.content
            # =================================================================
            # GOOGLE GEMINI
            # =================================================================
            elif "gemini" in target_model:
                api_key = os.getenv("GEMINI_API_KEY")
                if not api_key:
                    print(" [!] ERROR: GEMINI_API_KEY not found.")
                    return '{"draft": "Missing API Key", "code": "sorry"}'

                client = genai.Client(api_key=api_key)
                
                # Construct simple string prompt from messages
                system_instruction = messages[0]['content']
                user_msg = messages[1]['content']
                full_prompt = f"{system_instruction}\n\n{user_msg}"

                # New Generate Content Call
                response = client.models.generate_content(
                    model=target_model,
                    contents=full_prompt,
                    config=types.GenerateContentConfig(
                        response_mime_type='application/json', # Strict JSON
                        max_output_tokens=MAX_TOKENS,
                        temperature=0.2
                    )
                )
                return response.text

        except Exception as e:
            print(f"    [!] API Error ({self.llm_name}): {e}")
            return '{"draft": "API Error", "code": "sorry"}'

        return '{"draft": "Unknown API Model", "code": "sorry"}'
    
    def _append_llm_specific_instructions(self, messages: List[Dict[str, str]]) -> List[Dict[str, str]]:
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
            messages[1]["content"] += "\n\n### Instructions:\n" + cot_instruction
        else:
            messages[0]["content"] += "\n\n" + json_schema
        return messages