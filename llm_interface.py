import torch
from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig
from typing import Dict, List, Any, Optional, Tuple

# ============================================================================
# MODEL INTERFACE
# ============================================================================

class ModelInterface:
    """Singleton-style interface to handle model loading and generation."""
    
    def __init__(self, llm_name: str):
        self.llm_name = llm_name.lower()
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

    def generate(self, messages: List[Dict[str, str]]) -> str:
        """
        Routes the generation request to the correct backend (Local vs API).
        """
        if self.llm_name in ["deepseek-prover-v2", "goedel-prover-v2"]:
            return self._generate_local(messages)
        else:
            return self._generate_api(messages)

    def _generate_local(self, messages: List[Dict[str, str]]) -> str:
        inputs = self.tokenizer.apply_chat_template(
            messages, 
            tokenize=True, 
            add_generation_prompt=True, 
            return_tensors="pt"
        ).to(self.model.device)

        outputs = self.model.generate(
            inputs, 
            max_new_tokens=8192,
            pad_token_id=self.tokenizer.eos_token_id
        )
        
        # Decode only the new tokens
        generated_ids = outputs[0][inputs.shape[1]:]
        response = self.tokenizer.decode(generated_ids, skip_special_tokens=True)
        return response

    def _generate_api(self, messages: List[Dict[str, str]]) -> str:
        """Placeholder for API calls."""
        # TODO: Implement actual API calls here (OpenAI, VertexAI, etc.)
        # return call_api(self.llm_name, messages)
        return '{"draft": "API not implemented", "code": "sorry"}'