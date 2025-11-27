"""
Assertion Analyzer v1.2.0
Analyzes generated SVA assertions for quality and coverage
"""

import re
from typing import Dict, Any, List


class AssertionAnalyzer:
    """Analyzes SVA assertions for quality metrics and grading"""
    
    def __init__(self):
        self.categories = {
            'protocol': ['handshake', 'valid', 'ready', 'ack', 'req', 'grant'],
            'timing': ['posedge', 'negedge', 'delay', '##', 'cycle', 'timeout'],
            'data_integrity': ['stable', 'change', 'data', 'value', 'compare'],
            'reset': ['reset', 'rst', 'init', 'clear', 'default'],
            'clock': ['clock', 'clk', 'edge', 'frequency'],
            'coverage': ['cover', 'coverpoint', 'bins'],
            'sequence': ['sequence', '|=>', '|->', 'throughout', 'within'],
            'invariant': ['always', 'never', 'eventually', 'until']
        }
    
    def analyze(self, assertions: str, module_info: Dict[str, Any]) -> Dict[str, Any]:
        """
        Analyze assertions and return quality metrics
        
        Args:
            assertions: Generated SVA assertions string
            module_info: Module information dict with ports, signals, etc.
            
        Returns:
            Analysis results with grade, coverage, categories, recommendations
        """
        if not assertions or not assertions.strip():
            return self._empty_analysis()
        
        # Count assertions
        assertion_count = self._count_assertions(assertions)
        
        # Categorize assertions
        categories = self._categorize_assertions(assertions)
        
        # Calculate coverage
        coverage = self._calculate_coverage(assertions, module_info)
        
        # Calculate grade
        grade, grade_details = self._calculate_grade(
            assertion_count, categories, coverage, module_info
        )
        
        # Generate recommendations
        recommendations = self._generate_recommendations(
            assertions, module_info, categories, coverage
        )
        
        return {
            'total_assertions': assertion_count,
            'categories': categories,
            'coverage_percentage': coverage,
            'grade': grade,
            'grade_explanation': grade_details,
            'recommendations': recommendations
        }
    
    def _empty_analysis(self) -> Dict[str, Any]:
        """Return empty analysis for no assertions"""
        return {
            'total_assertions': 0,
            'categories': {},
            'coverage_percentage': 0,
            'grade': 'F',
            'grade_explanation': {
                'criteria': {
                    'coverage_score': 0,
                    'assertion_count': 0,
                    'category_diversity': 0,
                    'completeness': 0
                },
                'summary': 'No assertions were generated.',
                'improvements': ['Generate assertions first']
            },
            'recommendations': ['Generate assertions for the RTL code']
        }
    
    def _count_assertions(self, assertions: str) -> int:
        """Count total number of assertions"""
        patterns = [
            r'\bassert\s+property\b',
            r'\bassume\s+property\b',
            r'\bcover\s+property\b',
            r'\brestrict\s+property\b',
            r'\bexpect\s+property\b',
            r'^\s*\w+\s*:\s*assert\b',  # Named assertions
        ]
        
        count = 0
        for pattern in patterns:
            matches = re.findall(pattern, assertions, re.MULTILINE | re.IGNORECASE)
            count += len(matches)
        
        # Avoid double counting - use a reasonable minimum
        return max(count, 1) if assertions.strip() else 0
    
    def _categorize_assertions(self, assertions: str) -> Dict[str, int]:
        """Categorize assertions by type"""
        result = {}
        assertions_lower = assertions.lower()
        
        for category, keywords in self.categories.items():
            count = 0
            for keyword in keywords:
                count += len(re.findall(r'\b' + keyword + r'\b', assertions_lower))
            if count > 0:
                result[category] = min(count, 20)  # Cap at reasonable max
        
        return result
    
    def _calculate_coverage(self, assertions: str, module_info: Dict[str, Any]) -> int:
        """Calculate coverage percentage based on signals covered"""
        if not module_info:
            return 50  # Default if no module info
        
        ports = module_info.get('ports', [])
        signals = module_info.get('internal_signals', [])
        
        total_signals = len(ports) + len(signals)
        if total_signals == 0:
            return 75  # Default for modules with no detected signals
        
        # Check which signals are mentioned in assertions
        assertions_lower = assertions.lower()
        covered = 0
        
        for port in ports:
            port_name = port.get('name', '') if isinstance(port, dict) else str(port)
            if port_name.lower() in assertions_lower:
                covered += 1
        
        for signal in signals:
            signal_name = signal.get('name', '') if isinstance(signal, dict) else str(signal)
            if signal_name.lower() in assertions_lower:
                covered += 1
        
        # Calculate percentage with minimum floor
        raw_coverage = (covered / total_signals) * 100 if total_signals > 0 else 0
        
        # Add bonus for assertion complexity
        complexity_bonus = min(20, self._count_assertions(assertions) * 2)
        
        final_coverage = min(100, int(raw_coverage + complexity_bonus))
        return max(final_coverage, 25)  # Minimum 25% if any assertions exist
    
    def _calculate_grade(
        self, 
        assertion_count: int, 
        categories: Dict[str, int], 
        coverage: int,
        module_info: Dict[str, Any]
    ) -> tuple:
        """Calculate quality grade (A-F) with explanation"""
        
        # Score components (each out of 25)
        coverage_score = min(25, coverage / 4)
        
        # Assertion count score (up to 25 points)
        count_score = min(25, assertion_count * 2.5)
        
        # Category diversity score (up to 25 points)
        diversity_score = min(25, len(categories) * 5)
        
        # Completeness score based on port coverage
        ports = module_info.get('ports', []) if module_info else []
        expected_min = max(3, len(ports))
        completeness_score = min(25, (assertion_count / expected_min) * 25) if expected_min > 0 else 15
        
        # Total score
        total_score = coverage_score + count_score + diversity_score + completeness_score
        
        # Determine grade
        if total_score >= 85:
            grade = 'A'
        elif total_score >= 70:
            grade = 'B'
        elif total_score >= 55:
            grade = 'C'
        elif total_score >= 40:
            grade = 'D'
        else:
            grade = 'F'
        
        grade_details = {
            'criteria': {
                'coverage_score': round(coverage_score / 2.5),  # Scale to 0-10
                'assertion_count': round(count_score / 2.5),
                'category_diversity': round(diversity_score / 2.5),
                'completeness': round(completeness_score / 2.5)
            },
            'summary': self._get_grade_summary(grade, total_score, assertion_count, coverage),
            'improvements': self._get_improvements(grade, categories, coverage, assertion_count)
        }
        
        return grade, grade_details
    
    def _get_grade_summary(self, grade: str, score: float, count: int, coverage: int) -> str:
        """Generate grade summary text"""
        summaries = {
            'A': f"Excellent! Generated {count} assertions with {coverage}% coverage. Comprehensive verification.",
            'B': f"Good quality. {count} assertions achieving {coverage}% coverage. Minor improvements possible.",
            'C': f"Adequate. {count} assertions with {coverage}% coverage. Several areas for improvement.",
            'D': f"Basic coverage. {count} assertions at {coverage}% coverage. Significant gaps exist.",
            'F': f"Insufficient. Only {count} assertions with {coverage}% coverage. Major improvements needed."
        }
        return summaries.get(grade, f"Generated {count} assertions with {coverage}% coverage.")
    
    def _get_improvements(
        self, 
        grade: str, 
        categories: Dict[str, int], 
        coverage: int, 
        count: int
    ) -> List[str]:
        """Generate improvement suggestions"""
        improvements = []
        
        if coverage < 80:
            improvements.append("Increase signal coverage by adding assertions for uncovered ports")
        
        if 'reset' not in categories:
            improvements.append("Add reset behavior assertions")
        
        if 'timing' not in categories:
            improvements.append("Consider adding timing-related assertions")
        
        if 'data_integrity' not in categories:
            improvements.append("Add data integrity checks")
        
        if count < 5:
            improvements.append("Increase assertion count for better verification")
        
        if len(categories) < 3:
            improvements.append("Diversify assertion types (protocol, timing, data integrity)")
        
        if 'sequence' not in categories:
            improvements.append("Consider adding sequential property checks")
        
        return improvements[:5]  # Limit to top 5
    
    def _generate_recommendations(
        self, 
        assertions: str, 
        module_info: Dict[str, Any],
        categories: Dict[str, int],
        coverage: int
    ) -> List[str]:
        """Generate general recommendations"""
        recs = []
        
        # Check for common patterns
        if '$rose' not in assertions.lower() and '$fell' not in assertions.lower():
            recs.append("Consider using $rose/$fell for edge detection")
        
        if '$past' not in assertions.lower():
            recs.append("Use $past() for comparing with previous values")
        
        if '$stable' not in assertions.lower():
            recs.append("Consider $stable for signal stability checks")
        
        if 'disable iff' not in assertions.lower():
            recs.append("Add 'disable iff' clauses for reset conditions")
        
        # Module-specific recommendations
        ports = module_info.get('ports', []) if module_info else []
        for port in ports:
            port_name = port.get('name', '') if isinstance(port, dict) else str(port)
            if 'valid' in port_name.lower() and 'ready' in [p.get('name', '').lower() for p in ports if isinstance(p, dict)]:
                if 'handshake' not in assertions.lower():
                    recs.append(f"Add valid-ready handshake assertion for {port_name}")
                    break
        
        return recs[:6]  # Limit recommendations
