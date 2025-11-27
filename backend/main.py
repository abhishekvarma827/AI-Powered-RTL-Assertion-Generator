"""
RTL Assertion Generator Backend - FIXED VERSION
Compatible with llm_interface.py
"""

from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
from typing import Optional, Dict, Any, List
import os
import json
from datetime import datetime

# Import local modules
from rtl_parser import RTLParser
from llm_interface import LLMInterface
from assertion_analyzer import AssertionAnalyzer
from testbench_generator import TestbenchGenerator
from example_designs import get_example_code, get_example_designs

app = FastAPI(
    title="RTL Assertion Generator",
    version="2.0.0",
    description="Generate SystemVerilog Assertions from RTL code"
)

# CORS middleware
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Initialize components
rtl_parser = RTLParser()
llm_interface = LLMInterface()
analyzer = AssertionAnalyzer()
tb_generator = TestbenchGenerator()


# Request/Response Models
class ParseRequest(BaseModel):
    code: str


class GenerateRequest(BaseModel):
    code: str
    module_info: Dict[str, Any]
    model: str = "claude"


class TestbenchRequest(BaseModel):
    module_info: Dict[str, Any]
    assertions: str
    type: str = "simple"


class ExportRequest(BaseModel):
    assertions: str
    module_name: str
    format: str = "sv"
    analysis: Optional[Dict[str, Any]] = None


# Endpoints
@app.get("/")
async def root():
    return {
        "name": "RTL Assertion Generator",
        "version": "2.0.0",
        "status": "running"
    }


@app.post("/parse-rtl")
async def parse_rtl(request: ParseRequest):
    """Parse RTL code and extract module information"""
    try:
        module_info = rtl_parser.parse(request.code)
        return module_info
    except Exception as e:
        raise HTTPException(status_code=400, detail=str(e))


@app.post("/generate-assertions")
async def generate_assertions(request: GenerateRequest):
    """Generate SVA assertions using LLM - FIXED VERSION"""
    try:
        # Generate assertions - handle both old and new interface
        result = llm_interface.generate_assertions(
            code=request.code,
            module_info=request.module_info,
            model=request.model
        )
        
        # The new llm_interface returns just a string (backward compatible)
        assertions = result
        
        # Analyze the generated assertions
        analysis = analyzer.analyze(assertions, request.module_info)
        
        # Ensure grade is properly calculated
        if not analysis.get('grade') or analysis.get('grade') == 'N/A':
            coverage = analysis.get('coverage_percentage', 0)
            if coverage >= 90:
                analysis['grade'] = 'A'
            elif coverage >= 75:
                analysis['grade'] = 'B'
            elif coverage >= 60:
                analysis['grade'] = 'C'
            elif coverage >= 40:
                analysis['grade'] = 'D'
            else:
                analysis['grade'] = 'F'
        
        # Generate grade explanation if missing
        if not analysis.get('grade_explanation'):
            grade = analysis['grade']
            coverage = analysis.get('coverage_percentage', 0)
            total = analysis.get('total_assertions', 0)
            categories = analysis.get('categories', {})
            
            analysis['grade_explanation'] = {
                'criteria': {
                    'coverage_score': min(10, round(coverage / 10)),
                    'assertion_count': min(10, total),
                    'category_diversity': min(10, len(categories) * 2),
                    'completeness': 8 if grade in ['A', 'B'] else 5 if grade == 'C' else 3
                },
                'summary': f"Generated {total} assertions achieving {coverage}% coverage. "
                          f"Grade {grade} reflects {'excellent' if grade == 'A' else 'good' if grade == 'B' else 'adequate' if grade == 'C' else 'limited'} coverage.",
                'improvements': analysis.get('recommendations', [])
            }
        
        return {
            "assertions": assertions,
            "analysis": analysis
        }
    except Exception as e:
        # Better error reporting
        import traceback
        error_details = {
            "error": str(e),
            "type": type(e).__name__,
            "traceback": traceback.format_exc()
        }
        print(f"Error in generate_assertions: {error_details}")
        raise HTTPException(status_code=500, detail=str(e))


@app.post("/generate-testbench")
async def generate_testbench(request: TestbenchRequest):
    """Generate testbench wrapper for assertions"""
    try:
        testbench = tb_generator.generate(
            module_info=request.module_info,
            assertions=request.assertions,
            tb_type=request.type
        )
        return {"testbench": testbench}
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@app.post("/export")
async def export_assertions(request: ExportRequest):
    """Export assertions in various formats"""
    try:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        
        if request.format == "sv":
            content = f"""// ============================================
// RTL Assertion Generator v2.0
// Module: {request.module_name}
// Generated: {datetime.now().isoformat()}
// ============================================

{request.assertions}
"""
            filename = f"{request.module_name}_assertions_{timestamp}.sv"
            
        elif request.format == "txt":
            content = f"""RTL Assertion Generator v2.0
Module: {request.module_name}
Generated: {datetime.now().isoformat()}
{'=' * 50}

{request.assertions}
"""
            filename = f"{request.module_name}_assertions_{timestamp}.txt"
            
        elif request.format == "json":
            data = {
                "version": "2.0.0",
                "module_name": request.module_name,
                "generated_at": datetime.now().isoformat(),
                "assertions": request.assertions,
                "analysis": request.analysis
            }
            content = json.dumps(data, indent=2)
            filename = f"{request.module_name}_assertions_{timestamp}.json"
        else:
            raise HTTPException(status_code=400, detail=f"Unknown format: {request.format}")
        
        return {
            "content": content,
            "filename": filename
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@app.get("/examples")
async def list_examples():
    """List all available example designs"""
    return get_example_designs()


@app.get("/examples/{name}")
async def get_example(name: str):
    """Get a specific example design"""
    code = get_example_code(name)
    if not code:
        raise HTTPException(status_code=404, detail=f"Example not found: {name}")
    return {"code": code, "name": name}


if __name__ == "__main__":
    import uvicorn
    print("=" * 60)
    print("RTL Assertion Generator v2.0")
    print("=" * 60)
    uvicorn.run(app, host="0.0.0.0", port=8000)
