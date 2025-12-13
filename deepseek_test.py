from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig
import torch

torch.manual_seed(30)

formal_statement = r"""
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- What is the positive difference between $120\%$ of 30 and $130\%$ of 20? Show that it is 10.-/
theorem mathd_algebra_10 : abs ((120 : ℝ) / 100 * 30 - 130 / 100 * 20) = 10 := by
  sorry
""".strip()

prompt = """
Complete the following Lean 4 code:

```lean4
{}
```

Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
""".strip()

chat = [
  {"role": "user", "content": prompt.format(formal_statement)},
]

# 1. SETUP MODEL ID
# model_id = "deepseek-ai/DeepSeek-Prover-V2-7B"
model_id = "Goedel-LM/Goedel-Prover-V2-8B"

# 2. CONFIGURE 4-BIT QUANTIZATION (The Speed Fix)
quantization_config = BitsAndBytesConfig(
    load_in_4bit=True,
    bnb_4bit_quant_type="nf4",
    bnb_4bit_compute_dtype=torch.bfloat16,
    bnb_4bit_use_double_quant=True
)

# 3. LOAD TOKENIZER & FIX WARNINGS
tokenizer = AutoTokenizer.from_pretrained(model_id, trust_remote_code=True)
# Fix: Explicitly tell the model to use EOS as PAD
tokenizer.pad_token = tokenizer.eos_token
tokenizer.pad_token_id = tokenizer.eos_token_id

# 4. LOAD MODEL
model = AutoModelForCausalLM.from_pretrained(
    model_id, 
    quantization_config=quantization_config,
    device_map="auto", 
    trust_remote_code=True
)

inputs = tokenizer.apply_chat_template(chat, tokenize=True, add_generation_prompt=True, return_tensors="pt").to(model.device)

import time
start = time.time()
outputs = model.generate(inputs, max_new_tokens=8192)
print(tokenizer.batch_decode(outputs))
print(time.time() - start)
