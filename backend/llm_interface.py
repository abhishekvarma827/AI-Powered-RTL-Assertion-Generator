"""
LLM Interface - ULTIMATE VERSION FOR PERFECT ASSERTIONS
Features:
- Increased max tokens for large RTL
- Automatic RTL analysis and explanation
- World-class assertion generation prompt
- Comprehensive coverage guarantees
"""

import os
import time
import re
from typing import Dict, Any, List, Tuple, Optional

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
    """Ultimate LLM interface for world-class assertions"""
    
    # Increased token limits for large RTL designs
    MAX_TOKENS_GEMINI = 32768  # Increased from default
    MAX_TOKENS_ANTHROPIC = 16384  # Increased from 8192
    
    def __init__(self):
        self.gemini_model = None
        self.anthropic_client = None
        
        # Initialize Gemini
        if HAS_GENAI:
            api_key = os.environ.get('GOOGLE_API_KEY', '')
            if api_key and not api_key.startswith('your-'):
                genai.configure(api_key=api_key)
                self.gemini_model = genai.GenerativeModel('gemini-2.5-flash')
        
        # Initialize Anthropic
        if HAS_ANTHROPIC:
            api_key = os.environ.get('ANTHROPIC_API_KEY', '')
            if api_key and not api_key.startswith('your-'):
                self.anthropic_client = anthropic.Anthropic(api_key=api_key)
    
    def analyze_rtl(self, code: str, module_info: Dict[str, Any]) -> str:
        """
        Generate comprehensive RTL analysis and explanation.
        Called automatically when code is parsed.
        """
        analysis = self._deep_analyze(code, module_info)
        
        explanation = f"""
╔══════════════════════════════════════════════════════════════════════════╗
║                        RTL CODE ANALYSIS                                 ║
╚══════════════════════════════════════════════════════════════════════════╝

📌 MODULE: {module_info.get('name', 'Unknown')}

🏗️  ARCHITECTURE:
   • Module Type: {analysis['module_type'].upper()}
   • Clock Domain: {'Synchronous' if analysis.get('has_clock') else 'Combinational'}
   • Reset Style: {analysis.get('reset_style', 'None')}
   • Design Pattern: {', '.join(analysis['special_features']) if analysis['special_features'] else 'Standard Logic'}

📊 INTERFACE:
   • Total Ports: {len(module_info.get('ports', []))}
   • Inputs: {len([p for p in module_info.get('ports', []) if p['direction'] == 'input'])}
   • Outputs: {len([p for p in module_info.get('ports', []) if p['direction'] == 'output'])}
   • Parameters: {len(module_info.get('parameters', []))}

⚙️  DETECTED FEATURES:
"""
        
        if 'fifo' in analysis['special_features']:
            explanation += """
   🔷 FIFO (First-In-First-Out) Buffer
      - Circular buffer with read/write pointers
      - Handles data queuing with flow control
      - Critical: Data integrity, overflow/underflow prevention
      - Pointers: """ + ', '.join(analysis['pointers']) + "\n"
        
        if 'fsm' in analysis['special_features']:
            explanation += """
   🔷 Finite State Machine (FSM)
      - Sequential control logic with states
      - State transitions based on inputs
      - Critical: State coverage, transition correctness
      - State Variables: """ + ', '.join(analysis['state_variables']) + "\n"
        
        if 'counter' in analysis['special_features']:
            explanation += """
   🔷 Counter Logic
      - Counting/tracking mechanism detected
      - Critical: Increment/decrement, wraparound, bounds
      - Counter Signals: """ + ', '.join(analysis['counters']) + "\n"
        
        if 'arithmetic' in analysis['special_features']:
            explanation += """
   🔷 Arithmetic/ALU Operations
      - Mathematical computations present
      - Critical: Correctness, overflow, edge cases
      - Requires local variable capture for verification
"""
        
        if 'memory' in analysis['special_features']:
            explanation += """
   🔷 Memory/Storage Element
      - RAM/ROM or memory array detected
      - Critical: Read/write coherency, address bounds
"""
        
        explanation += f"""
🎯 VERIFICATION PRIORITIES:
"""
        
        for idx, assertion_type in enumerate(analysis['critical_assertions'][:8], 1):
            explanation += f"   {idx}. {assertion_type.replace('_', ' ').title()}\n"
        
        if len(analysis['critical_assertions']) > 8:
            explanation += f"   ... and {len(analysis['critical_assertions']) - 8} more checks\n"
        
        explanation += f"""
🔍 DATA PATHS:
"""
        if analysis['data_paths']:
            for dp in analysis['data_paths'][:5]:
                explanation += f"   • {dp['direction']:6} - {dp['name']:20} [{dp['width']}]\n"
            if len(analysis['data_paths']) > 5:
                explanation += f"   ... and {len(analysis['data_paths']) - 5} more data paths\n"
        else:
            explanation += "   • Mostly control logic\n"
        
        explanation += f"""
⚡ CONTROL SIGNALS:
   • {', '.join(analysis['control_signals'][:10]) if analysis['control_signals'] else 'None detected'}

🚨 ERROR/STATUS SIGNALS:
   • {', '.join(analysis['error_conditions']) if analysis['error_conditions'] else 'None detected'}

💡 DESIGN INTENT:
   {self._infer_design_intent(analysis, module_info)}

✅ RECOMMENDED ASSERTION STRATEGY:
   {self._get_assertion_strategy(analysis)}

╚══════════════════════════════════════════════════════════════════════════╝
"""
        
        return explanation
    
    def _infer_design_intent(self, analysis: Dict[str, Any], module_info: Dict[str, Any]) -> str:
        """Infer what the module is designed to do"""
        module_name = module_info.get('name', '').lower()
        
        if 'fifo' in analysis['special_features']:
            return "Data buffering and flow control between clock domains or rate-mismatched interfaces"
        elif 'fsm' in analysis['special_features']:
            return "Sequential control logic managing system state transitions"
        elif 'counter' in analysis['special_features']:
            return "Event counting or timing control mechanism"
        elif 'arithmetic' in analysis['special_features']:
            return "Mathematical computation or data processing"
        elif 'alu' in module_name:
            return "Arithmetic Logic Unit for mathematical operations"
        elif 'controller' in module_name or 'ctrl' in module_name:
            return "Control logic managing system behavior"
        elif 'memory' in analysis['special_features']:
            return "Data storage and retrieval"
        else:
            return "General digital logic processing"
    
    def _get_assertion_strategy(self, analysis: Dict[str, Any]) -> str:
        """Recommend assertion approach"""
        strategy = []
        
        if analysis['module_type'] == 'combinational':
            strategy.append("Use immediate (|->) assertions")
        else:
            strategy.append("Use concurrent assertions with proper timing (|=>)")
        
        if 'fifo' in analysis['special_features']:
            strategy.append("Focus on data integrity and pointer management")
        if 'fsm' in analysis['special_features']:
            strategy.append("Cover all states and transitions")
        if 'arithmetic' in analysis['special_features']:
            strategy.append("Capture inputs with local variables")
        
        strategy.append("Add comprehensive cover properties (15+ recommended)")
        
        return " | ".join(strategy)
    
    def generate_assertions(
        self, 
        code: str, 
        module_info: Dict[str, Any],
        model: str = "gemini",
        show_analysis: bool = True,
        return_analysis: bool = False
    ) -> str:
        """
        Generate world-class assertions with optional analysis output.
        
        Args:
            code: RTL code to analyze
            module_info: Parsed module information
            model: LLM model to use ("gemini" or "claude")
            show_analysis: If True, prints RTL analysis to console
            return_analysis: If True, returns tuple (assertions, analysis)
        
        Returns:
            str: Generated assertions code (or tuple if return_analysis=True)
        """
        
        # Always perform deep analysis
        analysis = self._deep_analyze(code, module_info)
        
        # Generate RTL explanation
        rtl_analysis = self.analyze_rtl(code, module_info)
        
        # Print analysis if requested
        if show_analysis:
            print(rtl_analysis)
        
        # Build the ultimate prompt
        prompt = self._build_ultimate_prompt(code, module_info, analysis)
        
        # Generate with validation
        raw = self._generate_with_validation(prompt, model, max_attempts=3)
        
        # Post-process
        fixed = self._post_process(raw, analysis)
        
        # Return based on flag
        if return_analysis:
            return fixed, rtl_analysis
        else:
            return fixed
    
    def _deep_analyze(self, code: str, module_info: Dict[str, Any]) -> Dict[str, Any]:
        """Deep analysis to identify ALL assertion opportunities"""
        
        analysis = {
            'module_type': None,
            'timing': None,
            'has_clock': False,
            'has_reset': False,
            'reset_style': 'None',
            'special_features': [],
            'critical_assertions': [],
            'state_variables': [],
            'counters': [],
            'pointers': [],
            'data_paths': [],
            'control_signals': [],
            'error_conditions': [],
        }
        
        code_lower = code.lower()
        
        # === Clock and Reset Detection ===
        ports = module_info.get('ports', [])
        analysis['has_clock'] = any('clk' in p['name'].lower() for p in ports)
        analysis['has_reset'] = any('rst' in p['name'].lower() for p in ports)
        
        if analysis['has_reset']:
            reset_port = next((p for p in ports if 'rst' in p['name'].lower()), None)
            if reset_port and 'n' in reset_port['name'].lower():
                analysis['reset_style'] = 'Active Low'
            else:
                analysis['reset_style'] = 'Active High'
        
        # === Module Type Detection ===
        has_always_ff = 'always_ff' in code_lower or '@(posedge' in code_lower
        has_always_comb = 'always_comb' in code_lower
        has_assign = 'assign' in code and not has_always_ff
        
        if has_always_ff:
            analysis['module_type'] = 'sequential'
            analysis['timing'] = '|=>'
        elif has_always_comb or (has_assign and not has_always_ff):
            analysis['module_type'] = 'combinational'
            analysis['timing'] = '|->'
        else:
            analysis['module_type'] = 'mixed'
            analysis['timing'] = 'mixed'
        
        # === Special Feature Detection ===
        if 'fifo' in code_lower or ('wr_pointer' in code_lower and 'rd_pointer' in code_lower):
            analysis['special_features'].append('fifo')
            analysis['critical_assertions'].extend([
                'data_integrity',
                'no_overflow',
                'no_underflow',
                'pointer_wraparound',
                'full_empty_logic',
                'status_counter_accuracy',
                'simultaneous_read_write',
                'empty_on_reset',
                'pointer_equality_when_empty'
            ])
            ptr_matches = re.findall(r'(wr_pointer|rd_pointer|write_ptr|read_ptr|wr_ptr|rd_ptr)', code_lower)
            analysis['pointers'] = list(set(ptr_matches))
        
        if 'typedef enum' in code_lower or ('state' in code_lower and 'case' in code_lower):
            analysis['special_features'].append('fsm')
            analysis['critical_assertions'].extend([
                'reset_to_initial_state',
                'all_states_reachable',
                'no_illegal_transitions',
                'output_stability',
                'state_coverage',
                'one_hot_encoding_check',
                'no_deadlock_states'
            ])
            state_match = re.search(r'(\w+_state|state|current_state|next_state)\s*[;,]', code_lower)
            if state_match:
                analysis['state_variables'].append(state_match.group(1))
        
        if any(x in code_lower for x in ['count', 'counter']):
            analysis['special_features'].append('counter')
            analysis['critical_assertions'].extend([
                'count_increment',
                'count_decrement',
                'count_wraparound',
                'count_bounds',
                'reset_count',
                'count_enable_hold'
            ])
            cnt_matches = re.findall(r'(count\w*|cnt\w*)', code_lower)
            analysis['counters'] = list(set(cnt_matches))
        
        if any(x in code_lower for x in ['div', 'mult', 'alu', 'add', 'sub']):
            analysis['special_features'].append('arithmetic')
            analysis['critical_assertions'].extend([
                'mathematical_correctness',
                'overflow_detection',
                'underflow_detection',
                'division_by_zero',
                'result_latency',
                'input_capture'
            ])
        
        if 'memory' in code_lower or 'ram' in code_lower or 'rom' in code_lower:
            analysis['special_features'].append('memory')
            analysis['critical_assertions'].extend([
                'write_read_coherency',
                'address_bounds',
                'write_enable_check',
                'read_enable_check',
                'no_x_propagation'
            ])
        
        # === Control Signal Detection ===
        for port in ports:
            name_lower = port['name'].lower()
            if any(x in name_lower for x in ['enable', 'en', 'valid', 'ready']):
                analysis['control_signals'].append(port['name'])
            if any(x in name_lower for x in ['full', 'empty', 'overflow', 'underflow', 'error']):
                analysis['error_conditions'].append(port['name'])
        
        # === Data Path Detection ===
        for port in ports:
            if port['direction'] in ['input', 'output']:
                width = port.get('width', '1')
                if width != '1' or 'data' in port['name'].lower():
                    analysis['data_paths'].append({
                        'name': port['name'],
                        'direction': port['direction'],
                        'width': width
                    })
        
        return analysis
    
    def _build_ultimate_prompt(self, code: str, module_info: Dict[str, Any], 
                               analysis: Dict[str, Any]) -> str:
        """Build the most comprehensive prompt for perfect assertions"""
        
        module_name = module_info.get('name', 'module')
        ports = module_info.get('ports', [])
        parameters = module_info.get('parameters', [])
        
        # Get clock and reset
        has_clock = analysis['has_clock']
        has_reset = analysis['has_reset']
        clock = next((p['name'] for p in ports if 'clk' in p['name'].lower()), 'clk')
        reset = next((p['name'] for p in ports if 'rst' in p['name'].lower()), 'rst_n')
        reset_active = f"!{reset}" if 'n' in reset.lower() else reset
        
        # Build parameter string
        param_list = self._build_param_string(parameters, code)
        
        # Build port declarations
        port_decls = self._build_port_declarations(ports)
        
        return f"""You are a WORLD-CLASS verification engineer with 20+ years of experience.
Your task: Generate PRODUCTION-GRADE SystemVerilog Assertions that would pass the most rigorous code reviews at companies like NVIDIA, Intel, AMD, Apple.

═══════════════════════════════════════════════════════════════════════════
                           📋 MODULE SPECIFICATION
═══════════════════════════════════════════════════════════════════════════

Module Name: {module_name}
Architecture: {analysis['module_type'].upper()} logic
Clock Domain: {'Clocked (posedge {})'.format(clock) if has_clock else 'Combinational'}
Reset: {'{} ({})'.format(reset, analysis['reset_style']) if has_reset else 'No reset'}
Design Pattern: {', '.join(analysis['special_features']).upper() if analysis['special_features'] else 'GENERAL LOGIC'}

RTL CODE TO VERIFY:
```systemverilog
{code}
```

═══════════════════════════════════════════════════════════════════════════
                        🎯 ASSERTION REQUIREMENTS
═══════════════════════════════════════════════════════════════════════════

Your assertions MUST achieve:
✓ 100% functional coverage of all operations
✓ All corner cases and edge conditions verified
✓ Safety properties (no overflow, underflow, illegal states)
✓ Liveness properties (progress guarantees)
✓ Data integrity across all paths
✓ Reset behavior for every output signal
✓ Minimum 15 cover properties for scenario coverage

═══════════════════════════════════════════════════════════════════════════
                    ⚡ CRITICAL TIMING RULES (MUST FOLLOW)
═══════════════════════════════════════════════════════════════════════════

COMBINATIONAL LOGIC (always_comb, assign):
   → Use |-> (implies, same cycle)
   → Output = f(inputs) happens IMMEDIATELY
   → Example: assign out = a & b;
              assert property (@(posedge clk) a && b |-> out);
   
SEQUENTIAL LOGIC (always_ff, @posedge):
   → Use |=> (overlapping implication, next cycle)
   → Output updates on NEXT clock edge
   → Example: always_ff @(posedge clk) q <= d;
              assert property (@(posedge clk) disable iff (!rst_n)
                  d |=> q);

MULTI-CYCLE OPERATIONS:
   → Use ##[m:n] for variable latency
   → Capture inputs with local variables
   → Example: (start, cap_a = a) ##[1:5] done |-> result == cap_a * 2

MIXED MODULES:
   → Analyze EACH signal's path individually
   → Combinational path: use |->
   → Registered path: use |=>

═══════════════════════════════════════════════════════════════════════════
                    🔧 MODULE-SPECIFIC REQUIREMENTS
═══════════════════════════════════════════════════════════════════════════

{self._build_detailed_requirements(analysis, clock, reset, reset_active)}

═══════════════════════════════════════════════════════════════════════════
                    📐 ASSERTION BEST PRACTICES
═══════════════════════════════════════════════════════════════════════════

1. NAMING CONVENTION:
   ✓ a_<category>_<description>  (e.g., a_fifo_no_overflow)
   ✓ p_<category>_<description>  (property)
   ✓ c_<scenario>                (cover)

2. RESET ASSERTIONS:
   ✓ NO "disable iff" clause in reset checks
   ✓ Verify EVERY output reaches known state
   ✓ Format: @(posedge clk) reset_active |-> output == reset_value;

3. FUNCTIONAL ASSERTIONS:
   ✓ Clear trigger → expected result pattern
   ✓ Use descriptive names
   ✓ Add meaningful $error messages

4. ARITHMETIC/LATENCY:
   ✓ ALWAYS capture inputs with local variables
   ✓ Use ##[min:max] for variable latency
   ✓ Verify mathematical correctness

5. SAFETY PROPERTIES:
   ✓ Bounds checking (array indices, pointers)
   ✓ Overflow/underflow detection
   ✓ Mutex properties (e.g., not full AND empty)

6. COVER PROPERTIES:
   ✓ Minimum 15 cover statements
   ✓ Cover: normal ops, edge cases, errors, corner cases
   ✓ Ensure reachability of all interesting states

═══════════════════════════════════════════════════════════════════════════
                    🏗️ OUTPUT MODULE STRUCTURE
═══════════════════════════════════════════════════════════════════════════

module {module_name}_assertions {param_list}(
{chr(10).join(port_decls)}
);

    //═══════════════════════════════════════════════════════════
    // SECTION 1: RESET BEHAVIOR VERIFICATION
    //═══════════════════════════════════════════════════════════
    // Verify all outputs reach their reset values
    // CRITICAL: No "disable iff" on reset assertions!
    
    {self._generate_reset_section(ports, clock, reset, reset_active, has_reset)}

    //═══════════════════════════════════════════════════════════
    // SECTION 2: FUNCTIONAL CORRECTNESS
    //═══════════════════════════════════════════════════════════
    // Verify core functionality and data transformations
    
    {self._generate_functional_section(analysis, clock, reset_active, has_clock, has_reset)}

    //═══════════════════════════════════════════════════════════
    // SECTION 3: SAFETY PROPERTIES
    //═══════════════════════════════════════════════════════════
    // Prevent illegal states and out-of-bounds conditions
    
    {self._generate_safety_section(analysis, clock, reset_active, has_clock, has_reset)}

    //═══════════════════════════════════════════════════════════
    // SECTION 4: DATA INTEGRITY & COHERENCY
    //═══════════════════════════════════════════════════════════
    // Ensure data written = data read (for FIFOs, memories)
    
    {self._generate_data_integrity_section(analysis, clock, reset_active)}

    //═══════════════════════════════════════════════════════════
    // SECTION 5: CONTROL SIGNAL VERIFICATION
    //═══════════════════════════════════════════════════════════
    // Verify handshaking, flow control, status flags
    
    {self._generate_control_section(analysis, clock, reset_active, has_clock, has_reset)}

    //═══════════════════════════════════════════════════════════
    // SECTION 6: STATE COVERAGE (FSM specific)
    //═══════════════════════════════════════════════════════════
    
    {self._generate_fsm_section(analysis, clock, reset_active) if 'fsm' in analysis['special_features'] else '// Not applicable - no FSM detected'}

    //═══════════════════════════════════════════════════════════
    // SECTION 7: COMPREHENSIVE COVER PROPERTIES
    //═══════════════════════════════════════════════════════════
    // MINIMUM 15 cover properties to ensure scenario coverage
    
    {self._generate_comprehensive_covers(analysis, clock)}

endmodule : {module_name}_assertions

═══════════════════════════════════════════════════════════════════════════
                        ⚠️ CRITICAL REMINDERS
═══════════════════════════════════════════════════════════════════════════

COMMON MISTAKES TO AVOID:
❌ Using |=> for combinational logic (use |->)
❌ Using |-> for sequential logic (use |=>)
❌ Adding disable iff to reset assertions
❌ Not capturing inputs for sequential arithmetic
❌ Forgetting pointer wraparound checks (FIFOs)
❌ Missing data integrity verification (FIFOs/memories)
❌ Insufficient cover properties (need 15+)
❌ Port list mismatch with RTL
❌ Vague assertion names
❌ Missing $error messages

QUALITY CHECKLIST:
[ ] Every output has reset assertion
[ ] Correct timing operator (|-> vs |=>) for EVERY assertion
[ ] All critical functional paths verified
[ ] Safety checks for bounds, overflow, underflow
[ ] Data integrity for storage elements
[ ] Control signals verified (full, empty, valid, ready)
[ ] 15+ meaningful cover properties
[ ] Proper local variable capture for arithmetic
[ ] Clear, descriptive names and error messages
[ ] Comprehensive comments explaining each assertion

═══════════════════════════════════════════════════════════════════════════

🎯 YOUR MISSION:
Generate the COMPLETE, PRODUCTION-READY assertion module that would receive
a perfect score in verification review. Every assertion must be:
  • Syntactically correct
  • Semantically meaningful
  • Properly timed (|-> vs |=>)
  • Well-documented
  • Covering real bugs

Generate ONLY the SystemVerilog code. No markdown, no explanations outside comments.
Make this the BEST assertion module you've ever written.

BEGIN GENERATION NOW:
"""

    def _build_detailed_requirements(self, analysis: Dict[str, Any], 
                                     clock: str, reset: str, reset_active: str) -> str:
        """Build comprehensive module-specific requirements"""
        
        requirements = []
        
        if 'fifo' in analysis['special_features']:
            requirements.append(f"""
🔷 FIFO MODULE - MANDATORY ASSERTIONS:

1. DATA INTEGRITY (HIGHEST PRIORITY):
   property p_fifo_data_integrity;
       logic [DATA_WIDTH-1:0] stored_data;
       @(posedge {clock}) disable iff ({reset_active})
       (wr_cs && wr_en && !full, stored_data = data_in) |->
       ##[1:RAM_DEPTH] (rd_cs && rd_en && data_out == stored_data);
   endproperty
   a_fifo_data_integrity: assert property (p_fifo_data_integrity);

2. NO WRITE WHEN FULL:
   a_fifo_no_write_when_full: assert property (
       @(posedge {clock}) disable iff ({reset_active})
       full && wr_cs && wr_en |=> $stable(wr_pointer)
   );

3. NO READ WHEN EMPTY:
   a_fifo_no_read_when_empty: assert property (
       @(posedge {clock}) disable iff ({reset_active})
       empty && rd_cs && rd_en |=> $stable(rd_pointer)
   );

4. POINTER WRAPAROUND:
   a_fifo_wr_ptr_wrap: assert property (
       @(posedge {clock}) disable iff ({reset_active})
       (wr_pointer == (RAM_DEPTH-1)) && wr_cs && wr_en |=> (wr_pointer == 0)
   );

5. STATUS COUNTER BOUNDS:
   a_fifo_count_bounds: assert property (
       @(posedge {clock}) disable iff ({reset_active})
       status_cnt <= RAM_DEPTH
   );

6. FULL/EMPTY CORRECTNESS:
   a_fifo_full_correct: assert property (
       @(posedge {clock}) disable iff ({reset_active})
       full == (status_cnt == RAM_DEPTH)
   );
   a_fifo_empty_correct: assert property (
       @(posedge {clock}) disable iff ({reset_active})
       empty == (status_cnt == 0)
   );

7. SIMULTANEOUS READ/WRITE:
   Cover and verify behavior when reading and writing simultaneously

8. POINTER EQUALITY WHEN EMPTY:
   When empty, rd_pointer should equal wr_pointer (for some FIFO designs)
""")
        
        if 'fsm' in analysis['special_features']:
            requirements.append(f"""
🔷 FINITE STATE MACHINE - MANDATORY ASSERTIONS:

1. RESET TO IDLE STATE:
   a_fsm_reset_state: assert property (
       @(posedge {clock}) {reset_active} |-> state == IDLE
   );

2. STATE VALIDITY:
   Always verify current state is a legal/defined state value

3. TRANSITION COVERAGE:
   Cover EVERY possible state transition

4. OUTPUT STABILITY:
   Outputs should be stable within each state (not glitching)

5. NO ILLEGAL TRANSITIONS:
   Create assertions for transitions that should NEVER occur

6. ONE-HOT ENCODING (if applicable):
   Verify exactly one bit is high in one-hot encoded states

7. DEADLOCK PREVENTION:
   Ensure no state can become permanently stuck
""")
        
        if 'counter' in analysis['special_features']:
            requirements.append(f"""
🔷 COUNTER MODULE - MANDATORY ASSERTIONS:

1. INCREMENT CORRECTNESS:
   When increment enabled: count |=> $past(count) + 1

2. DECREMENT CORRECTNESS:
   When decrement enabled: count |=> $past(count) - 1

3. WRAPAROUND BEHAVIOR:
   At MAX: verify wraparound to 0 (or hold if no wraparound)

4. UNDERFLOW PROTECTION:
   At 0: verify behavior on decrement

5. ENABLE HOLD:
   When disabled: count should remain stable

6. BOUNDS CHECKING:
   Count should never exceed defined maximum
""")
        
        if 'arithmetic' in analysis['special_features']:
            requirements.append(f"""
🔷 ARITHMETIC/ALU MODULE - MANDATORY ASSERTIONS:

1. MATHEMATICAL CORRECTNESS (with input capture):
   property p_add_correct;
       logic [WIDTH-1:0] cap_a, cap_b;
       @(posedge {clock}) disable iff ({reset_active})
       (start, cap_a = a, cap_b = b) ##[1:LATENCY] done
       |-> (result == (cap_a + cap_b));
   endproperty

2. OVERFLOW DETECTION:
   Verify overflow flag when result exceeds maximum

3. UNDERFLOW DETECTION:
   Verify underflow for subtraction results < 0

4. DIVISION BY ZERO:
   Verify proper handling (error flag or defined behavior)

5. LATENCY VERIFICATION:
   Result appears exactly after specified cycles

6. RESULT STABILITY:
   Result remains stable until next operation
""")
        
        if 'memory' in analysis['special_features']:
            requirements.append(f"""
🔷 MEMORY MODULE - MANDATORY ASSERTIONS:

1. WRITE-READ COHERENCY:
   Data written to address should read back correctly

2. ADDRESS BOUNDS:
   Verify address never exceeds memory depth

3. WRITE ENABLE CHECK:
   Write only occurs when write_enable is high

4. NO X PROPAGATION:
   Outputs should never be X or Z in normal operation

5. READ DURING WRITE:
   Define and verify behavior for same-address read/write
""")
        
        if not requirements:
            requirements.append("""
🔷 GENERAL MODULE - RECOMMENDED ASSERTIONS:

1. INPUT-OUTPUT RELATIONSHIPS:
   Verify all documented functional behaviors

2. BOUNDARY CONDITIONS:
   Test minimum and maximum input values

3. STABILITY CHECKS:
   Outputs should not glitch when inputs are stable

4. MUTUAL EXCLUSION:
   Verify mutually exclusive conditions never occur together
""")
        
        return '\n'.join(requirements)
    
    def _build_param_string(self, parameters: List[Dict[str, Any]], code: str) -> str:
        """Build parameter declaration string"""
        if not parameters:
            return ""
        
        param_strs = []
        for param in parameters:
            # Try to extract default value from code
            default = param.get('default', '8')
            param_strs.append(f"{param['name']} = {default}")
        
        return f" #(parameter {', '.join(param_strs)})"
    
    def _build_port_declarations(self, ports: List[Dict[str, Any]]) -> List[str]:
        """Build port declaration strings"""
        port_decls = []
        for p in ports:
            width = p.get('width', '1')
            ptype = p.get('type', 'logic')
            if width == '1':
                port_decls.append(f"    {p['direction']}  {ptype}                 {p['name']}")
            else:
                port_decls.append(f"    {p['direction']}  {ptype} [{width}] {p['name']}")
        return port_decls
    
    def _generate_reset_section(self, ports, clock, reset, reset_active, has_reset) -> str:
        """Generate reset assertion section"""
        if not has_reset:
            return "// No reset in module"
        
        output_ports = [p for p in ports if p['direction'] == 'output']
        templates = []
        
        for port in output_ports[:3]:
            templates.append(f"""
    property p_reset_{port['name']};
        @(posedge {clock})
        {reset_active} |-> {port['name']} == <reset_value>;
    endproperty
    a_reset_{port['name']}: assert property (p_reset_{port['name']})
        else $error("Reset: {port['name']} not at expected value");""")
        
        if len(output_ports) > 3:
            templates.append(f"\n    // ... Add reset assertions for remaining {len(output_ports)-3} outputs")
        
        return ''.join(templates)
    
    def _generate_functional_section(self, analysis, clock, reset_active, has_clock, has_reset) -> str:
        """Generate functional assertion section"""
        if not has_clock:
            return """
    // Use immediate assertions for combinational logic
    always_comb begin
        a_main_function: assert (<condition>) else $error("Function check failed");
    end"""
        
        timing_op = analysis['timing']
        disable_clause = f"disable iff ({reset_active})" if has_reset else ""
        
        return f"""
    property p_main_function;
        @(posedge {clock}) {disable_clause}
        <trigger_condition> {timing_op} <expected_result>;
    endproperty
    a_main_function: assert property (p_main_function)
        else $error("Main function verification failed");"""
    
    def _generate_safety_section(self, analysis, clock, reset_active, has_clock, has_reset) -> str:
        """Generate safety assertion section"""
        if not has_clock:
            return "// No safety checks needed for pure combinational"
        
        templates = []
        disable_clause = f"disable iff ({reset_active})" if has_reset else ""
        
        if analysis['error_conditions']:
            for signal in analysis['error_conditions'][:2]:
                templates.append(f"""
    a_safety_{signal}: assert property (
        @(posedge {clock}) {disable_clause}
        <appropriate_condition_for_{signal}>
    ) else $error("{signal} safety violation");""")
        
        return ''.join(templates) if templates else "// Add safety checks as needed"
    
    def _generate_data_integrity_section(self, analysis, clock, reset_active) -> str:
        """Generate data integrity section"""
        if 'fifo' not in analysis['special_features'] and 'memory' not in analysis['special_features']:
            return "// Not applicable for this module type"
        
        return f"""
    // CRITICAL: Verify data written equals data read
    property p_data_integrity;
        logic [DATA_WIDTH-1:0] stored_data;
        @(posedge {clock}) disable iff ({reset_active})
        (wr_cs && wr_en && !full, stored_data = data_in) |->
        ##[1:RAM_DEPTH] (rd_cs && rd_en && data_out == stored_data);
    endproperty
    a_data_integrity: assert property (p_data_integrity)
        else $error("Data integrity violation: written data != read data");"""
    
    def _generate_control_section(self, analysis, clock, reset_active, has_clock, has_reset) -> str:
        """Generate control signal section"""
        if not analysis['control_signals'] and not analysis['error_conditions']:
            return "// No specific control signals to verify"
        
        templates = []
        disable_clause = f"disable iff ({reset_active})" if has_reset else ""
        
        if 'fifo' in analysis['special_features']:
            templates.append(f"""
    // FIFO full/empty flag verification
    a_not_full_and_empty: assert property (
        @(posedge {clock}) {disable_clause}
        !(full && empty)
    ) else $error("FIFO cannot be both full and empty");""")
        
        return ''.join(templates) if templates else "// Add control signal checks as needed"
    
    def _generate_fsm_section(self, analysis, clock, reset_active) -> str:
        """Generate FSM-specific section"""
        state_var = analysis['state_variables'][0] if analysis['state_variables'] else 'state'
        
        return f"""
    // FSM State Coverage
    property p_all_states_reachable;
        // Cover each state
        @(posedge {clock})
        ({state_var} == STATE_VALUE);
    endproperty
    
    // Add cover properties for each state
    // Add transition assertions"""
    
    def _generate_comprehensive_covers(self, analysis, clock) -> str:
        """Generate comprehensive cover properties"""
        covers = [f"""
    // COVER PROPERTIES - Minimum 15 required
    
    // Normal Operations
    cover property (@(posedge {clock}) <normal_operation_1>);
    cover property (@(posedge {clock}) <normal_operation_2>);
    cover property (@(posedge {clock}) <normal_operation_3>);
    
    // Edge Cases
    cover property (@(posedge {clock}) <edge_case_1>);
    cover property (@(posedge {clock}) <edge_case_2>);
    cover property (@(posedge {clock}) <edge_case_3>);
    
    // Corner Cases
    cover property (@(posedge {clock}) <corner_case_1>);
    cover property (@(posedge {clock}) <corner_case_2>);
    cover property (@(posedge {clock}) <corner_case_3>);
    
    // Error Scenarios
    cover property (@(posedge {clock}) <error_scenario_1>);
    cover property (@(posedge {clock}) <error_scenario_2>);
    cover property (@(posedge {clock}) <error_scenario_3>);
"""]
        
        if 'fifo' in analysis['special_features']:
            covers.append("""
    // FIFO-specific covers
    cover property (@(posedge {}) write_when_not_full);
    cover property (@(posedge {}) read_when_not_empty);
    cover property (@(posedge {}) simultaneous_read_write);
""".format(clock, clock, clock))
        
        if 'fsm' in analysis['special_features']:
            covers.append("""
    // FSM-specific covers
    cover property (@(posedge {}) state_transition_1);
    cover property (@(posedge {}) state_transition_2);
""".format(clock, clock))
        
        return ''.join(covers)
    
    def _generate_with_validation(self, prompt: str, model: str, max_attempts: int) -> str:
        """Generate with retry and basic validation"""
        for attempt in range(max_attempts):
            try:
                if model == "gemini" and self.gemini_model:
                    raw = self._call_gemini(prompt)
                elif model == "claude" and self.anthropic_client:
                    raw = self._call_anthropic(prompt)
                else:
                    return self._generate_fallback_enhanced()
                
                # Basic validation
                if 'module' in raw and 'endmodule' in raw:
                    return raw
                    
            except Exception as e:
                if attempt < max_attempts - 1:
                    time.sleep(2 ** attempt)
                else:
                    print(f"Warning: All generation attempts failed: {e}")
                    return self._generate_fallback_enhanced()
        
        return self._generate_fallback_enhanced()
    
    def _post_process(self, assertions: str, analysis: Dict[str, Any]) -> str:
        """Enhanced post-processing with validation"""
        
        # Remove markdown
        assertions = re.sub(r'```systemverilog\n?', '', assertions)
        assertions = re.sub(r'```\n?', '', assertions)
        
        # Fix common timing mistakes
        if analysis['module_type'] == 'combinational':
            # Should use |-> not |=>
            assertions = re.sub(r'\|\s*=\s*>', '|->', assertions)
        elif analysis['module_type'] == 'sequential':
            # For sequential, |=> is usually correct
            pass
        
        # Fix 'next' keyword
        assertions = re.sub(r'\|->\\s*next\\s*\\(([^)]+)\\)', r'|=> \\1', assertions)
        
        # Ensure proper spacing
        assertions = re.sub(r'(\|\-\>|\|\=\>)', r' \1 ', assertions)
        
        return assertions.strip()
    
    def _call_gemini(self, prompt: str, max_retries: int = 3) -> str:
        """Call Gemini API with retry logic and increased token limit"""
        generation_config = {
            'max_output_tokens': self.MAX_TOKENS_GEMINI,
            'temperature': 0.2,  # Lower temperature for more consistent code
        }
        
        for attempt in range(max_retries):
            try:
                response = self.gemini_model.generate_content(
                    prompt,
                    generation_config=generation_config
                )
                return response.text
            except Exception as e:
                if attempt < max_retries - 1:
                    time.sleep(2 ** attempt)
                else:
                    raise e
        return ""
    
    def _call_anthropic(self, prompt: str, max_retries: int = 3) -> str:
        """Call Anthropic API with retry logic and increased token limit"""
        for attempt in range(max_retries):
            try:
                response = self.anthropic_client.messages.create(
                    model="claude-sonnet-4-20250514",
                    max_tokens=self.MAX_TOKENS_ANTHROPIC,
                    temperature=0.2,  # Lower temperature for more consistent code
                    messages=[{"role": "user", "content": prompt}]
                )
                return response.content[0].text
            except Exception as e:
                if attempt < max_retries - 1:
                    time.sleep(2 ** attempt)
                else:
                    raise e
        return ""
    
    def _generate_fallback_enhanced(self) -> str:
        """Enhanced fallback with basic structure"""
        return """module module_assertions (
    // Configure API key for better results
    // This is a fallback template
);
    // Reset Assertions
    // Functional Assertions
    // Safety Checks
    // Cover Properties
endmodule"""
    def get_rtl_feedback(
        self, 
        code: str, 
        module_info: Dict[str, Any],
        assertions: Optional[str] = None,
        model: str = "claude"
    ) -> str:
        """
        Provide comprehensive feedback on RTL code and generated assertions
        
        Args:
            code: The RTL source code
            module_info: Parsed module information
            assertions: Generated assertions (optional)
            model: LLM model to use
            
        Returns:
            Detailed feedback string
        """
        
        # Build feedback prompt
        prompt = self._build_feedback_prompt(code, module_info, assertions)
        
        try:
            if model == "gemini" and self.gemini_model:
                feedback = self._call_gemini(prompt)
            elif model == "claude" and self.anthropic_client:
                feedback = self._call_anthropic(prompt)
            else:
                feedback = self._generate_fallback_feedback(module_info, assertions)
            
            # Clean up markdown formatting
            feedback = self._clean_markdown(feedback)
            
            return feedback
            
        except Exception as e:
            print(f"Error generating feedback: {e}")
            return self._generate_fallback_feedback(module_info, assertions)
    
    def _build_feedback_prompt(
        self, 
        code: str, 
        module_info: Dict[str, Any],
        assertions: Optional[str]
    ) -> str:
        """Build the prompt for feedback generation"""
        
        module_name = module_info.get('name', 'Unknown')
        ports = module_info.get('ports', [])
        
        prompt = f"""You are an expert RTL verification engineer. Analyze the following SystemVerilog/Verilog RTL code and provide comprehensive feedback.

=== RTL CODE ===
{code}

=== MODULE INFORMATION ===
Name: {module_name}
Ports: {len(ports)}
"""
        
        if assertions:
            prompt += f"""
=== GENERATED ASSERTIONS ===
{assertions}
"""
        
        prompt += """
=== PROVIDE DETAILED FEEDBACK ON ===

1. RTL Code Quality
   - Design patterns and best practices
   - Potential issues or bugs
   - Coding style and readability
   - Clock domain crossing issues (if any)
   - Reset handling
   - Linting warnings or common pitfalls

2. Functional Correctness
   - Logic errors or edge cases
   - Potential race conditions
   - Unintended latches or combinational loops
   - State machine issues (if present)
   - Data path integrity

3. Verification Concerns
   - Hard-to-verify scenarios
   - Missing corner case coverage
   - Testability issues
   - Assertion coverage gaps

4. Recommendations
   - Design improvements
   - Additional assertions needed
   - Best practices to follow
   - Common verification pitfalls to avoid

IMPORTANT: Format your response in PLAIN TEXT without markdown formatting. Do NOT use ** for bold, _ for italics, or ``` for code blocks. Use simple text with clear sections and bullet points using - or *.
Highlight any CRITICAL issues that must be addressed."""
        
        return prompt
    
    def _generate_fallback_feedback(
        self, 
        module_info: Dict[str, Any],
        assertions: Optional[str]
    ) -> str:
        """Generate basic fallback feedback when LLM is unavailable"""
        
        module_name = module_info.get('name', 'Unknown')
        ports = module_info.get('ports', [])
        num_ports = len(ports)
        
        feedback = f"""
╔══════════════════════════════════════════════════════════════════════════╗
║                        RTL FEEDBACK REPORT                                ║
╚══════════════════════════════════════════════════════════════════════════╝

📊 Module: {module_name}
🔌 Total Ports: {num_ports}

⚠️  API Configuration Required
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

To receive AI-powered feedback on your RTL code and assertions, please
configure your API keys:

• ANTHROPIC_API_KEY for Claude analysis
• GOOGLE_API_KEY for Gemini analysis

✅ BASIC ANALYSIS (Without API)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

✓ Module structure detected: {module_name}
✓ Port count: {num_ports} port(s)
"""
        
        # Add clock/reset detection
        has_clock = any('clk' in p.get('name', '').lower() for p in ports)
        has_reset = any('rst' in p.get('name', '').lower() or 'reset' in p.get('name', '').lower() for p in ports)
        
        if has_clock:
            feedback += "✓ Clock signal detected\n"
        else:
            feedback += "⚠ No clock signal detected (combinational logic?)\n"
            
        if has_reset:
            feedback += "✓ Reset signal detected\n"
        else:
            feedback += "⚠ No reset signal detected\n"
        
        if assertions:
            feedback += f"""
✓ Assertions have been generated

💡 RECOMMENDATIONS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. Review generated assertions for completeness
2. Add testbench to validate assertions
3. Consider edge cases specific to your design
4. Configure API key for AI-powered analysis
"""
        else:
            feedback += """
⚠ No assertions generated yet

💡 NEXT STEPS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. Click "Generate Assertions" to create SVA properties
2. Review the generated assertions
3. Generate testbench for validation
"""
        
        feedback += """
╚══════════════════════════════════════════════════════════════════════════╝
"""
        
        return feedback
    
    def _clean_markdown(self, text: str) -> str:
        """
        Remove markdown formatting from text
        
        Args:
            text: Text potentially containing markdown formatting
            
        Returns:
            Clean text without markdown formatting
        """
        if not text:
            return text
        
        # Remove bold (**text** or __text__)
        text = re.sub(r'\*\*([^\*]+)\*\*', r'\1', text)
        text = re.sub(r'__([^_]+)__', r'\1', text)
        
        # Remove italic (*text* or _text_) - be careful not to remove bullet points
        text = re.sub(r'(?<!\*)\*([^\*\n]+)\*(?!\*)', r'\1', text)
        text = re.sub(r'(?<!_)_([^_\n]+)_(?!_)', r'\1', text)
        
        # Remove code blocks (```code```)
        text = re.sub(r'```[^\n]*\n(.*?)```', r'\1', text, flags=re.DOTALL)
        
        # Remove inline code (`code`)
        text = re.sub(r'`([^`]+)`', r'\1', text)
        
        # Remove markdown headers (keep the text, remove #)
        text = re.sub(r'^#+\s+', '', text, flags=re.MULTILINE)
        
        # Remove [link](url) - keep just the link text
        text = re.sub(r'\[([^\]]+)\]\([^\)]+\)', r'\1', text)
        
        # Clean up any remaining double asterisks or underscores
        text = re.sub(r'\*\*', '', text)
        text = re.sub(r'__', '', text)
        
        return text
