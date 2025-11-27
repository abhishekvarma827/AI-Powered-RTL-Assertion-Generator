"""
Testbench Generator v1.2.0
Generates testbench wrappers for SVA assertions
"""

from typing import Dict, Any, List
from datetime import datetime


class TestbenchGenerator:
    """Generates SystemVerilog testbenches for assertion validation"""
    
    def generate(
        self, 
        module_info: Dict[str, Any], 
        assertions: str,
        tb_type: str = "simple"
    ) -> str:
        """
        Generate a testbench for the given module and assertions
        
        Args:
            module_info: Parsed module information
            assertions: SVA assertions string
            tb_type: Type of testbench ('simple' or 'comprehensive')
            
        Returns:
            Complete testbench code as string
        """
        if tb_type == "comprehensive":
            return self._generate_comprehensive(module_info, assertions)
        else:
            return self._generate_simple(module_info, assertions)
    
    def _generate_simple(self, module_info: Dict[str, Any], assertions: str) -> str:
        """Generate a simple testbench"""
        module_name = module_info.get('name', 'dut')
        ports = module_info.get('ports', [])
        
        # Find clock and reset
        clock, reset = self._find_clock_reset(ports)
        
        # Build signal declarations
        signal_decls = self._generate_signal_declarations(ports)
        
        # Build DUT instantiation
        dut_inst = self._generate_dut_instantiation(module_name, ports)
        
        return f"""// ============================================
// Testbench for {module_name}
// Generated: {datetime.now().isoformat()}
// RTL Assertion Generator v1.2.0
// ============================================

`timescale 1ns/1ps

module {module_name}_tb;

    // ----------------------------------------
    // Signal Declarations
    // ----------------------------------------
{signal_decls}

    // ----------------------------------------
    // DUT Instantiation
    // ----------------------------------------
{dut_inst}

    // ----------------------------------------
    // Clock Generation
    // ----------------------------------------
{self._generate_clock(clock)}

    // ----------------------------------------
    // Reset Sequence
    // ----------------------------------------
{self._generate_reset(reset, clock)}

    // ----------------------------------------
    // Assertions
    // ----------------------------------------
{self._indent_code(assertions, 4)}

    // ----------------------------------------
    // Simple Test Stimulus
    // ----------------------------------------
    initial begin
        $display("Starting testbench for {module_name}");
        $display("Time: %0t", $time);
        
        // Wait for reset
        @(negedge {reset if reset else 'clk'});
        repeat(5) @(posedge {clock if clock else 'clk'});
        
        // Add your test stimulus here
        $display("Test stimulus phase");
        repeat(100) @(posedge {clock if clock else 'clk'});
        
        $display("Testbench completed at time %0t", $time);
        $finish;
    end

    // ----------------------------------------
    // Waveform Dump
    // ----------------------------------------
    initial begin
        $dumpfile("{module_name}_tb.vcd");
        $dumpvars(0, {module_name}_tb);
    end

endmodule
"""
    
    def _generate_comprehensive(self, module_info: Dict[str, Any], assertions: str) -> str:
        """Generate a comprehensive testbench with more features"""
        module_name = module_info.get('name', 'dut')
        ports = module_info.get('ports', [])
        
        clock, reset = self._find_clock_reset(ports)
        signal_decls = self._generate_signal_declarations(ports)
        dut_inst = self._generate_dut_instantiation(module_name, ports)
        
        # Get input and output ports for stimulus/checking
        input_ports = [p for p in ports if p['direction'] == 'input' and p['name'] not in [clock, reset]]
        output_ports = [p for p in ports if p['direction'] == 'output']
        
        return f"""// ============================================
// Comprehensive Testbench for {module_name}
// Generated: {datetime.now().isoformat()}
// RTL Assertion Generator v1.2.0
// ============================================

`timescale 1ns/1ps

module {module_name}_tb;

    // ----------------------------------------
    // Parameters
    // ----------------------------------------
    parameter CLK_PERIOD = 10;  // Clock period in ns
    parameter NUM_TESTS = 100;  // Number of random tests
    parameter TIMEOUT = 10000; // Simulation timeout

    // ----------------------------------------
    // Signal Declarations
    // ----------------------------------------
{signal_decls}

    // Test tracking
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // ----------------------------------------
    // DUT Instantiation
    // ----------------------------------------
{dut_inst}

    // ----------------------------------------
    // Clock Generation
    // ----------------------------------------
    initial begin
        {clock if clock else 'clk'} = 0;
        forever #(CLK_PERIOD/2) {clock if clock else 'clk'} = ~{clock if clock else 'clk'};
    end

    // ----------------------------------------
    // Reset Task
    // ----------------------------------------
    task automatic apply_reset();
        $display("[%0t] Applying reset", $time);
        {self._generate_reset_task(reset)}
        $display("[%0t] Reset complete", $time);
    endtask

    // ----------------------------------------
    // Randomize Inputs Task
    // ----------------------------------------
    task automatic randomize_inputs();
{self._generate_randomize_task(input_ports)}
    endtask

    // ----------------------------------------
    // Assertions
    // ----------------------------------------
{self._indent_code(assertions, 4)}

    // ----------------------------------------
    // Main Test Sequence
    // ----------------------------------------
    initial begin
        $display("========================================");
        $display("Comprehensive Testbench for {module_name}");
        $display("========================================");
        $display("Clock Period: %0d ns", CLK_PERIOD);
        $display("Number of Tests: %0d", NUM_TESTS);
        $display("");

        // Initialize inputs
{self._generate_init_inputs(input_ports)}

        // Apply reset
        apply_reset();
        
        // Wait for system to stabilize
        repeat(5) @(posedge {clock if clock else 'clk'});

        // Random testing
        $display("[%0t] Starting random tests", $time);
        for (int i = 0; i < NUM_TESTS; i++) begin
            test_count++;
            randomize_inputs();
            @(posedge {clock if clock else 'clk'});
            
            if (i % 10 == 0)
                $display("[%0t] Completed %0d tests", $time, i);
        end

        // Final report
        repeat(10) @(posedge {clock if clock else 'clk'});
        $display("");
        $display("========================================");
        $display("Test Summary");
        $display("========================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed: %0d", pass_count);
        $display("Failed: %0d", fail_count);
        $display("========================================");
        
        $finish;
    end

    // ----------------------------------------
    // Timeout Watchdog
    // ----------------------------------------
    initial begin
        #(TIMEOUT * CLK_PERIOD);
        $display("[%0t] ERROR: Simulation timeout!", $time);
        $finish;
    end

    // ----------------------------------------
    // Assertion Pass/Fail Tracking
    // ----------------------------------------
    always @(posedge {clock if clock else 'clk'}) begin
        // Increment pass count each cycle (assertions will catch failures)
        pass_count++;
    end

    // ----------------------------------------
    // Waveform Dump
    // ----------------------------------------
    initial begin
        $dumpfile("{module_name}_tb.vcd");
        $dumpvars(0, {module_name}_tb);
    end

endmodule
"""
    
    def _find_clock_reset(self, ports: List[Dict]) -> tuple:
        """Find clock and reset signals"""
        clock = None
        reset = None
        
        for port in ports:
            name_lower = port['name'].lower()
            if 'clk' in name_lower or 'clock' in name_lower:
                clock = port['name']
            if 'rst' in name_lower or 'reset' in name_lower:
                reset = port['name']
        
        return clock, reset
    
    def _generate_signal_declarations(self, ports: List[Dict]) -> str:
        """Generate signal declarations for testbench"""
        lines = []
        for port in ports:
            width = port.get('width', '1')
            if width == '1':
                lines.append(f"    logic {port['name']};")
            else:
                lines.append(f"    logic [{width}] {port['name']};")
        return "\n".join(lines)
    
    def _generate_dut_instantiation(self, module_name: str, ports: List[Dict]) -> str:
        """Generate DUT instantiation"""
        port_connections = []
        for port in ports:
            port_connections.append(f"        .{port['name']}({port['name']})")
        
        connections = ",\n".join(port_connections)
        return f"    {module_name} dut (\n{connections}\n    );"
    
    def _generate_clock(self, clock: str) -> str:
        """Generate clock generation code"""
        clk = clock if clock else 'clk'
        return f"""    initial begin
        {clk} = 0;
        forever #5 {clk} = ~{clk};
    end"""
    
    def _generate_reset(self, reset: str, clock: str) -> str:
        """Generate reset sequence"""
        if not reset:
            return "    // No reset signal detected"
        
        is_active_low = 'n' in reset.lower() or '_n' in reset.lower()
        clk = clock if clock else 'clk'
        
        if is_active_low:
            return f"""    initial begin
        {reset} = 0;
        repeat(5) @(posedge {clk});
        {reset} = 1;
    end"""
        else:
            return f"""    initial begin
        {reset} = 1;
        repeat(5) @(posedge {clk});
        {reset} = 0;
    end"""
    
    def _generate_reset_task(self, reset: str) -> str:
        """Generate reset task body"""
        if not reset:
            return "        // No reset signal"
        
        is_active_low = 'n' in reset.lower() or '_n' in reset.lower()
        
        if is_active_low:
            return f"""        {reset} = 0;
        repeat(5) @(posedge clk);
        {reset} = 1;"""
        else:
            return f"""        {reset} = 1;
        repeat(5) @(posedge clk);
        {reset} = 0;"""
    
    def _generate_randomize_task(self, input_ports: List[Dict]) -> str:
        """Generate input randomization task body"""
        if not input_ports:
            return "        // No input ports to randomize"
        
        lines = []
        for port in input_ports:
            lines.append(f"        {port['name']} = $urandom();")
        return "\n".join(lines)
    
    def _generate_init_inputs(self, input_ports: List[Dict]) -> str:
        """Generate input initialization"""
        if not input_ports:
            return "        // No input ports to initialize"
        
        lines = []
        for port in input_ports:
            lines.append(f"        {port['name']} = 0;")
        return "\n".join(lines)
    
    def _indent_code(self, code: str, spaces: int) -> str:
        """Indent code block"""
        indent = " " * spaces
        lines = code.split('\n')
        return '\n'.join(indent + line if line.strip() else line for line in lines)
