import json
import re
from typing import Any, Dict, Optional


# ============================================================================
# ROBUST PARSING HELPER FUNCTIONS
# ============================================================================

def extract_json_from_response(text: str) -> Optional[Dict[str, Any]]:
    """Robustly extracts and fixes JSON from LLM responses."""
    def sanitize_json_string(match):
        content = match.group(0)
        content = content.replace('\n', '\\n').replace('\r', '').replace('\t', '\\t')
        return content

    def robust_parse(candidate_text):
        try:
            return json.loads(candidate_text)
        except json.JSONDecodeError:
            string_pattern = r'"(?:\\.|[^"\\])*"'
            repaired_text = re.sub(string_pattern, sanitize_json_string, candidate_text)
            try:
                return json.loads(repaired_text)
            except json.JSONDecodeError:
                return None

    code_block_pattern = r'```(?:json)?\s*(\{.*?\})\s*```'
    matches = re.findall(code_block_pattern, text, re.DOTALL)
    for match in matches:
        result = robust_parse(match)
        if result and "draft" in result and "code" in result:
            return result

    brace_matches = re.findall(r'\{.*\}', text, re.DOTALL)
    if brace_matches:
        candidate = brace_matches[-1]
        result = robust_parse(candidate)
        if result and "draft" in result and "code" in result:
            return result
    return None

def validate_schema(data: Any) -> bool:
    if not isinstance(data, dict): return False
    return "draft" in data and "code" in data

def extract_lean_code_from_response(text: str) -> Dict[str, str]:
    """Extracts Lean code from response for prover models."""
    patterns = [r'```lean4\s*\n(.*?)\n\s*```', r'```lean\s*\n(.*?)\n\s*```', r'```\s*\n(.*?)\n\s*```']
    
    code_block = None
    full_match = None

    for pattern in patterns:
        matches = re.findall(pattern, text, re.DOTALL)
        if matches:
            code_block = matches[-1]
            full_matches = re.finditer(pattern, text, re.DOTALL)
            for m in full_matches: full_match = m
            break

    if code_block:
        if full_match:
            draft = text[:full_match.start()] + text[full_match.end():]
        else:
            draft = text
        return {"draft": draft.strip(), "code":code_block.strip()}
    else:
        return {"draft": text.strip(), "code": "sorry"}
    
    
