"""
RTL Parser v1.2.0
Parses Verilog/SystemVerilog code to extract module information
"""

import re
from typing import Dict, Any, List, Optional


class RTLParser:
    """Parser for Verilog/SystemVerilog RTL code"""
    
    def __init__(self):
        self.port_patterns = [
            # SystemVerilog style: input logic [7:0] name
            r'(input|output|inout)\s+(logic|wire|reg)?\s*(\[\s*[\w\-\:\$\(\)]+\s*\])?\s*(\w+)',
            # Verilog style in port list: input [7:0] name
            r'(input|output|inout)\s*(\[\s*[\w\-\:\$\(\)]+\s*\])?\s*(\w+)',
        ]
        
        self.signal_patterns = [
            # wire/reg/logic declarations
            r'(wire|reg|logic)\s*(\[\s*[\w\-\:\$\(\)]+\s*\])?\s*(\w+)',
        ]
    
    def parse(self, code: str) -> Dict[str, Any]:
        """
        Parse RTL code and extract module information
        
        Args:
            code: Verilog/SystemVerilog source code
            
        Returns:
            Dictionary containing module name, ports, parameters, signals
        """
        if not code or not code.strip():
            raise ValueError("Empty RTL code provided")
        
        # Extract module name
        module_name = self._extract_module_name(code)
        if not module_name:
            raise ValueError("No module declaration found in RTL code")
        
        # Extract ports
        ports = self._extract_ports(code)
        
        # Extract parameters
        parameters = self._extract_parameters(code)
        
        # Extract internal signals
        signals = self._extract_internal_signals(code, ports)
        
        # Infer port types (clock, reset, data, control)
        ports = self._infer_port_types(ports)
        
        return {
            "name": module_name,
            "ports": ports,
            "parameters": parameters,
            "internal_signals": signals
        }
    
    def _extract_module_name(self, code: str) -> Optional[str]:
        """Extract module name from code"""
        # Match: module name or module name #(...)
        pattern = r'module\s+(\w+)\s*(?:#|\(|;)'
        match = re.search(pattern, code)
        return match.group(1) if match else None
    
    def _extract_ports(self, code: str) -> List[Dict[str, str]]:
        """Extract port declarations from code"""
        ports = []
        seen_ports = set()
        
        # Try to find the module port list first
        module_match = re.search(r'module\s+\w+\s*(?:#\s*\([^)]*\))?\s*\(([^;]*)\)\s*;', code, re.DOTALL)
        
        if module_match:
            port_section = module_match.group(1)
        else:
            port_section = code
        
        # SystemVerilog style ports
        sv_pattern = r'(input|output|inout)\s+(logic|wire|reg)?\s*(\[\s*[\w\-\+\:\$\(\)\s]+\])?\s*(\w+)'
        for match in re.finditer(sv_pattern, port_section):
            direction = match.group(1)
            data_type = match.group(2) or 'wire'
            width = match.group(3) or ''
            name = match.group(4)
            
            if name not in seen_ports:
                seen_ports.add(name)
                ports.append({
                    "name": name,
                    "direction": direction,
                    "type": data_type,
                    "width": self._clean_width(width)
                })
        
        # Also check for Verilog-2001 style declarations in module body
        if not ports:
            v2k_pattern = r'(input|output|inout)\s*(\[\s*[\w\-\+\:\$\(\)\s]+\])?\s*(\w+)\s*[,;)]'
            for match in re.finditer(v2k_pattern, code):
                direction = match.group(1)
                width = match.group(2) or ''
                name = match.group(3)
                
                if name not in seen_ports:
                    seen_ports.add(name)
                    ports.append({
                        "name": name,
                        "direction": direction,
                        "type": "wire",
                        "width": self._clean_width(width)
                    })
        
        return ports
    
    def _extract_parameters(self, code: str) -> List[Dict[str, Any]]:
        """Extract parameter declarations"""
        parameters = []
        
        # Match parameter declarations
        pattern = r'parameter\s+(?:(\w+)\s+)?(\w+)\s*=\s*([^,;\)]+)'
        for match in re.finditer(pattern, code):
            param_type = match.group(1) or 'integer'
            name = match.group(2)
            value = match.group(3).strip()
            
            parameters.append({
                "name": name,
                "type": param_type,
                "default": value
            })
        
        return parameters
    
    def _extract_internal_signals(self, code: str, ports: List[Dict]) -> List[Dict[str, str]]:
        """Extract internal signal declarations"""
        signals = []
        port_names = {p['name'] for p in ports}
        seen_signals = set()
        
        # Match wire/reg/logic declarations
        pattern = r'(wire|reg|logic)\s*(\[\s*[\w\-\+\:\$\(\)\s]+\])?\s*(\w+)\s*[;,=]'
        for match in re.finditer(pattern, code):
            signal_type = match.group(1)
            width = match.group(2) or ''
            name = match.group(3)
            
            # Skip if it's a port or already seen
            if name not in port_names and name not in seen_signals:
                seen_signals.add(name)
                signals.append({
                    "name": name,
                    "type": signal_type,
                    "width": self._clean_width(width)
                })
        
        return signals
    
    def _clean_width(self, width: str) -> str:
        """Clean up width specification"""
        if not width:
            return "1"
        # Remove brackets and clean up
        width = width.replace('[', '').replace(']', '').strip()
        return width if width else "1"
    
    def _infer_port_types(self, ports: List[Dict]) -> List[Dict]:
        """Infer semantic port types (clock, reset, data, control)"""
        for port in ports:
            name_lower = port['name'].lower()
            
            if any(clk in name_lower for clk in ['clk', 'clock']):
                port['semantic_type'] = 'clock'
            elif any(rst in name_lower for rst in ['rst', 'reset', 'arst', 'srst']):
                port['semantic_type'] = 'reset'
            elif any(ctrl in name_lower for ctrl in ['en', 'enable', 'sel', 'valid', 'ready', 'start', 'done', 'wr', 'rd']):
                port['semantic_type'] = 'control'
            else:
                port['semantic_type'] = 'data'
        
        return ports
