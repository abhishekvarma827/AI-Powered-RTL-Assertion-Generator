"""
LLM Interface - ULTIMATE FIXED VERSION
Handles BOTH sequential AND combinational logic perfectly
Generates A-grade assertions for ANY RTL module
"""

import os
import time
import re
from typing import Dict, Any

try:
    import google.generativeai as genai
    HAS_GENAI = True
except ImportError:
    HAS_GENAI = False

try:
    import anthropic
    HAS_ANTHROPIC = True
except ImportError:
    HAS_ANTHROPIC = False


class LLMInterface:
    """Ultimate LLM interface - handles all module types"""
    
    def __init__(self):
        self.gemini_model = None
        self.anthropic_client = None
        
        # Initialize Gemini
        if HAS_GENAI:
            api_key = os.environ.get('GOOGLE_API_KEY', '')
            if api_key and not api_key.startswith('your-'):
                genai.configure(api_key=api_key)
                self.gemini_model = genai.GenerativeModel('gemini-2.0-flash-exp')
        
        # Initialize Anthropic
        if HAS_ANTHROPIC:
            api_key = os.environ.get('ANTHROPIC_API_KEY', '')
            if api_key and not api_key.startswith('your-'):
                self.anthropic_client = anthropic.Anthropic(api_key=api_key)
    
    def generate_assertions(
        self, 
        code: str, 
        module_info: Dict[str, Any],
        model: str = "gemini"
    ) -> str:
        """Generate perfect assertions for ANY module type"""
        
        # Build the ultimate prompt
        prompt = self._build_ultimate_fixed_prompt(code, module_info)
        
        # Generate
        if model == "gemini" and self.gemini_model:
            raw = self._call_gemini(prompt)
        elif model == "claude" and self.anthropic_client:
            raw = self._call_anthropic(prompt)
        else:
            raw = self._generate_fallback(module_info)
        
        # Auto-fix
        fixed = self._auto_fix(raw)
        
        return fixed
    
    def _build_ultimate_fixed_prompt(self, code: str, module_info: Dict[str, Any]) -> str:
        """THE ULTIMATE FIXED PROMPT - handles sequential AND combinational"""
        
        module_name = module_info.get('name', 'module')
        ports = module_info.get('ports', [])
        parameters = module_info.get('parameters', [])
        
        # Analyze module type
        code_lower = code.lower()
        
        # Critical: Detect combinational vs sequential
        has_always_ff = 'always_ff' in code_lower
        has_always_comb = 'always_comb' in code_lower
        has_assign = 'assign' in code and not has_always_ff
        is_combinational = (has_always_comb or has_assign) and not has_always_ff
        is_sequential = has_always_ff or '@(posedge' in code_lower
        
        # Detect other characteristics
        is_fsm = 'typedef enum' in code_lower or ('state' in code_lower and 'case' in code_lower)
        is_counter = 'count' in code_lower and ('+=' in code or '- 1' in code or '+ 1' in code)
        is_arithmetic = any(x in module_name.lower() for x in ['div', 'mult', 'alu', 'add', 'sub'])
        
        # Find clock/reset
        has_clock = any('clk' in p['name'].lower() for p in ports)
        has_reset = any('rst' in p['name'].lower() for p in ports)
        
        clock = next((p['name'] for p in ports if 'clk' in p['name'].lower()), 'clk')
        reset = next((p['name'] for p in ports if 'rst' in p['name'].lower()), 'rst_n')
        reset_active = f"!{reset}" if 'n' in reset.lower() else reset
        
        # Build parameter list
        param_list = ""
        if parameters:
            param_lines = []
            for p in parameters:
                param_lines.append(f"    parameter {p.get('type', '')} {p['name']} = {p.get('default', '0')}")
            param_list = "#(\n" + ",\n".join(param_lines) + "\n)"
        elif 'parameter' in code:
            param_matches = re.findall(r'parameter\s+(?:(\w+)\s+)?(\w+)\s*=\s*([^,;\)]+)', code)
            if param_matches:
                param_lines = []
                for match in param_matches:
                    ptype = match[0] if match[0] else ''
                    pname = match[1]
                    pval = match[2].strip()
                    param_lines.append(f"    parameter {ptype} {pname} = {pval}".strip())
                param_list = "#(\n" + ",\n".join(param_lines) + "\n)"
        
        # Build port declarations
        port_decls = []
        for p in ports:
            width = p.get('width', '1')
            ptype = p.get('type', 'logic')
            if width == '1':
                port_decls.append(f"    {p['direction']}  {ptype}                 {p['name']}")
            else:
                port_decls.append(f"    {p['direction']}  {ptype} [{width}] {p['name']}")
        
        # Module-specific guidance based on analysis
        if is_combinational and not has_clock:
            specific = f"""
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
⚠️ CRITICAL: COMBINATIONAL MODULE (NO CLOCK/RESET)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

This module is PURELY COMBINATIONAL:
- Uses: always_comb or assign
- No registers, no clock, no reset
- Outputs respond IMMEDIATELY (same cycle)

YOUR TASK:
Generate a simple assertion module with IMMEDIATE assertions.

DO NOT add clock or reset to ports!
Use immediate assertions in always_comb blocks.

Example for combinational decoder:
```systemverilog
module {module_name}_assertions (
    // EXACT ports from original (no clk/rst!)
    {chr(10).join(port_decls)}
);

    // Immediate assertions for combinational logic
    always_comb begin
        if (enable) begin
            a_main: assert (output == expected_value)
                else $error("Output incorrect");
        end
    end
    
    // Can also use continuous checks
    assert property (@* output inside {{valid_values}})
        else $error("Output out of range");

endmodule
```

CRITICAL RULES:
1. ❌ DO NOT add clk or rst_n to ports
2. ❌ DO NOT use @(posedge clk) 
3. ❌ DO NOT use |=> or |->
4. ✅ USE immediate assertions in always_comb
5. ✅ USE assert (condition) directly
6. ✅ Match EXACT ports from original RTL
"""
        elif is_combinational and has_clock:
            specific = f"""
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
⚠️ CRITICAL: COMBINATIONAL WITH CLOCK
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

This module is COMBINATIONAL but has a clock:
- Uses: always_comb or assign
- Has clock (for synchronization)
- Outputs respond SAME CYCLE (not next cycle!)

TIMING RULE: USE |-> (SAME CYCLE), NOT |=>

Example:
```systemverilog
// ✅ CORRECT for combinational
property p_combo_check;
    @(posedge {clock}) disable iff ({reset_active})
    input_valid |-> output == expected;  // |-> same cycle!
endproperty

// ❌ WRONG - would use |=> for sequential only
property p_wrong;
    @(posedge {clock})
    input_valid |=> output == expected;  // Wrong! Next cycle
endproperty
```

CRITICAL:
- Always use |-> for all checks (same cycle response)
- Never use |=> (that's for sequential/registered outputs)
- Output changes IMMEDIATELY when inputs change
"""
        elif is_fsm:
            specific = f"""
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
🎯 STATE MACHINE (SEQUENTIAL)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

This is a SEQUENTIAL state machine.
Outputs update on NEXT CYCLE.

TIMING RULE: USE |=> (NEXT CYCLE)

MUST include:
1. Local variables to capture inputs
2. Mathematical correctness (for arithmetic)
3. Specific state transition conditions

Example:
```systemverilog
property p_state_trans;
    @(posedge {clock}) disable iff ({reset_active})
    state == IDLE && start |=> state == ACTIVE;  // |=> next cycle
endproperty

property p_correctness;
    logic [W-1:0] cap_in1, cap_in2;
    @(posedge {clock}) disable iff ({reset_active})
    (start, cap_in1 = input1, cap_in2 = input2)
    ##[1:$] done
    |-> (result == cap_in1 OP cap_in2);
endproperty
```
"""
        elif is_counter:
            specific = f"""
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
🎯 COUNTER (SEQUENTIAL)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

This is a SEQUENTIAL counter.
Count updates on NEXT CYCLE.

TIMING RULE: USE |=> (NEXT CYCLE)

Example:
```systemverilog
property p_increment;
    @(posedge {clock}) disable iff ({reset_active})
    enable && count < MAX |=> count == $past(count) + 1;  // |=> next
endproperty
```
"""
        elif is_sequential:
            specific = f"""
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
🎯 SEQUENTIAL LOGIC
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

This module has registers (always_ff).
Outputs update on NEXT CYCLE.

TIMING RULE: USE |=> (NEXT CYCLE)
"""
        else:
            specific = """
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
🎯 GENERAL LOGIC
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Analyze the RTL to determine timing.
"""
        
        return f"""You are the WORLD'S BEST verification engineer. Generate PERFECT assertions.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
📋 MODULE ANALYSIS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module: {module_name}
Type: {'COMBINATIONAL' if is_combinational else 'SEQUENTIAL' if is_sequential else 'MIXED'}
Has Clock: {'YES - ' + clock if has_clock else 'NO'}
Has Reset: {'YES - ' + reset if has_reset else 'NO'}
Always_comb: {'YES' if has_always_comb else 'NO'}
Always_ff: {'YES' if has_always_ff else 'NO'}
Assign statements: {'YES' if has_assign else 'NO'}

RTL Code:
```systemverilog
{code}
```

{specific}

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
⚡ TIMING OPERATORS - CRITICAL RULES
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

READ THIS CAREFULLY - THIS IS THE #1 MISTAKE:

🔴 COMBINATIONAL LOGIC (always_comb, assign):
✅ USE: |-> (same cycle)
❌ NEVER: |=> (that's for sequential!)

Example:
// Decoder, MUX, ALU (combinational):
enable |-> output == expected;  // ✅ CORRECT

🔵 SEQUENTIAL LOGIC (always_ff, has registers):
✅ USE: |=> (next cycle)  
❌ NEVER: |-> (that's for combinational!)

Example:
// Counter, FSM, registered output:
enable |=> count == $past(count) + 1;  // ✅ CORRECT

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
📐 OUTPUT FORMAT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module {module_name}_assertions {param_list if param_list else ''}(
{chr(10).join(port_decls)}
);

    {"// COMBINATIONAL MODULE - Use immediate assertions" if is_combinational and not has_clock else ""}
    {"// SEQUENTIAL MODULE - Use clocked properties" if is_sequential else ""}

    //===========================================
    // Reset Assertions (if has reset)
    //===========================================
    {"" if not has_reset else f'''property p_reset_<signal>;
        @(posedge {clock})
        {reset_active} |-> <signal> == <reset_value>;
    endproperty
    a_reset_<signal>: assert property (p_reset_<signal>);
    '''}
    
    //===========================================
    // Functional Assertions
    //===========================================
    {"" if not has_clock else f'''property p_main;
        @(posedge {clock}) {"disable iff (" + reset_active + ")" if has_reset else ""}
        <condition> {"|->" if is_combinational else "|=>"} <check>;  // {"SAME cycle" if is_combinational else "NEXT cycle"}
    endproperty
    a_main: assert property (p_main);
    '''}
    
    //===========================================
    // Correctness
    //===========================================
    {"// Use local variables for sequential arithmetic" if is_sequential and is_arithmetic else ""}
    {"// Direct checks for combinational" if is_combinational else ""}
    
    //===========================================
    // Cover Properties
    //===========================================
    // 6+ cover properties

endmodule

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
✅ CHECKLIST - VERIFY BEFORE RESPONDING
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Is this combinational (always_comb/assign)?
  → Use |-> for ALL checks
  → If no clock: use immediate assertions
  
Is this sequential (always_ff/registers)?
  → Use |=> for registered outputs
  → Use local variables for arithmetic
  
Ports match original RTL exactly?
  → Don't add clock/reset if RTL doesn't have them
  
Reset assertions have NO disable iff?
  → Only operational assertions use disable iff

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
🔥 EXAMPLES
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

COMBINATIONAL DECODER:
module decoder_assertions (
    input  logic [2:0] in,
    input  logic en,
    output logic [7:0] out
);
    // No clock/reset in original!
    always_comb begin
        if (en) begin
            a_decode: assert (out == (8'b1 << in))
                else $error("Decode error");
        end
    end
endmodule

COMBINATIONAL WITH CLOCK:
module mux_assertions (
    input logic clk,
    input logic [1:0] sel,
    output logic [7:0] out
);
    property p_select;
        @(posedge clk)
        sel == 0 |-> out == in0;  // |-> same cycle!
    endproperty
endmodule

SEQUENTIAL COUNTER:
module counter_assertions (
    input logic clk, rst_n, en,
    output logic [7:0] count
);
    property p_inc;
        @(posedge clk) disable iff (!rst_n)
        en |=> count == $past(count) + 1;  // |=> next cycle!
    endproperty
endmodule

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Generate ONLY the assertion module code.
Match ports EXACTLY to original RTL.
Use correct timing operator (|-> vs |=>).

Generate now:"""

    def _auto_fix(self, assertions: str) -> str:
        """Auto-fix common mistakes"""
        # Remove markdown
        assertions = re.sub(r'```systemverilog\n?', '', assertions)
        assertions = re.sub(r'```\n?', '', assertions)
        
        # Fix 'next' keyword
        assertions = re.sub(r'\|->\\s*next\\s*\\(([^)]+)\\)', r'|=> \\1', assertions)
        
        return assertions.strip()
    
    def _call_gemini(self, prompt: str, max_retries: int = 3) -> str:
        """Call Gemini API"""
        for attempt in range(max_retries):
            try:
                response = self.gemini_model.generate_content(prompt)
                return response.text
            except Exception as e:
                if attempt < max_retries - 1:
                    time.sleep(2 ** attempt)
                else:
                    raise e
        return ""
    
    def _call_anthropic(self, prompt: str, max_retries: int = 3) -> str:
        """Call Anthropic API"""
        for attempt in range(max_retries):
            try:
                response = self.anthropic_client.messages.create(
                    model="claude-sonnet-4-20250514",
                    max_tokens=8192,
                    messages=[{"role": "user", "content": prompt}]
                )
                return response.content[0].text
            except Exception as e:
                if attempt < max_retries - 1:
                    time.sleep(2 ** attempt)
                else:
                    raise e
        return ""
    
    def _generate_fallback(self, module_info: Dict[str, Any]) -> str:
        """Basic fallback"""
        module_name = module_info.get('name', 'module')
        ports = module_info.get('ports', [])
        
        port_lines = []
        for p in ports:
            width = p.get('width', '1')
            ptype = p.get('type', 'logic')
            if width == '1':
                port_lines.append(f"    {p['direction']}  {ptype}  {p['name']}")
            else:
                port_lines.append(f"    {p['direction']}  {ptype} [{width}] {p['name']}")
        
        return f"""module {module_name}_assertions (
{chr(10).join(port_lines)}
);
    // Configure API key for better results
endmodule"""
