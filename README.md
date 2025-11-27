# RTL Assertion Generator v1.2.0

A powerful tool for automatically generating SystemVerilog Assertions (SVA) from RTL code using LLM APIs.

## ✨ What's New in v1.2.0

### 1. Column-Based Example Browser
Navigate examples easily with a 3-column layout:
- **Category** (Combinational Logic, Sequential Logic, etc.)
- **Design** (Full Adder, Counter, FIFO, etc.)
- **RTL Style** (Behavioral, Dataflow, Structural)

### 2. Multi-Color Syntax Highlighting
Generated assertions now display with proper syntax highlighting:
- **Purple**: Keywords (module, always, if, etc.)
- **Red**: SVA keywords (assert, property, sequence)
- **Cyan**: SVA operators (|=>, |->, ##)
- **Teal**: System functions ($rose, $fell, $past)
- **Green**: Strings
- **Orange**: Numbers
- **Yellow**: Clock/Reset signals
- **Gray**: Comments

### 3. Fixed Grading System
Grade is always calculated (no more N/A):
- Click the grade card to see detailed breakdown
- Scores for: Coverage, Assertion Count, Category Diversity, Completeness
- Improvement suggestions included

## 🚀 Quick Start

### Prerequisites
- Python 3.9+
- Node.js 16+
- npm or yarn

### Backend Setup

```bash
cd backend
pip install -r requirements.txt

# Set API keys (optional - fallback assertions work without them)
export ANTHROPIC_API_KEY=your-key-here
export GOOGLE_API_KEY=your-key-here

# Run server
python main.py
# or
uvicorn main:app --reload --port 8000
```

### Frontend Setup

```bash
cd frontend
npm install
npm start
```

Open http://localhost:3000 in your browser.

## 📚 Example Designs

The tool includes 30+ pre-built RTL examples:

| Category | Designs |
|----------|---------|
| Combinational Logic | Half Adder, Full Adder, 2:1 MUX, 4:1 MUX, DEMUX |
| Encoders & Decoders | 4:2 Encoder, 8:3 Encoder, 2:4 Decoder, 3:8 Decoder |
| Sequential Logic | Up/Down Counter, BCD Counter, Simple FSM |
| Frequency Dividers | Divide by 2, Divide by N |
| Comparators | 1-bit, 4-bit, N-bit |
| Memory & Buffers | Sync FIFO, Async FIFO, Register File |

Each design is available in multiple RTL styles:
- **Behavioral**: Procedural always blocks
- **Dataflow**: Continuous assignments
- **Structural**: Gate-level primitives
- **Parameterized**: Configurable parameters

## 🎯 Features

### Core Features
- **Parse RTL**: Extract module info, ports, parameters, signals
- **Generate Assertions**: Create comprehensive SVA using LLM
- **Analyze Quality**: Grade assertions A-F with detailed breakdown
- **Export**: Save as .sv, .txt, or .json

### Analysis Metrics
- **Coverage %**: Percentage of signals covered by assertions
- **Categories**: Protocol, timing, data integrity, reset, etc.
- **Recommendations**: Suggestions for improvement

### Testbench Generation
- **Simple**: Basic clock/reset with stimulus template
- **Comprehensive**: Random testing, timeout watchdog, pass/fail tracking

## 🎨 Syntax Highlighting Colors

The syntax highlighter uses a Catppuccin-inspired color scheme:

| Element | Color | Hex Code |
|---------|-------|----------|
| Keywords | Mauve | `#cba6f7` |
| SVA Keywords | Red | `#f38ba8` |
| SVA Operators | Sky | `#89dceb` |
| System Functions | Teal | `#94e2d5` |
| Strings | Green | `#a6e3a1` |
| Numbers | Peach | `#fab387` |
| Comments | Overlay | `#6c7086` |
| Identifiers | Text | `#cdd6f4` |
| Clock/Reset | Yellow | `#f9e2af` |

## 📖 Usage

1. **Load Example** or paste your RTL code
2. Click **Parse RTL** to extract module info
3. Select LLM model (Claude or Gemini)
4. Click **Generate Assertions**
5. View highlighted assertions with grade
6. Export or generate testbench

## 🔧 API Endpoints

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/parse-rtl` | POST | Parse RTL code |
| `/generate-assertions` | POST | Generate SVA assertions |
| `/generate-testbench` | POST | Generate testbench |
| `/export` | POST | Export assertions |
| `/examples` | GET | List example designs |
| `/examples/{name}` | GET | Get specific example |

## 📁 Project Structure

```
rtl-assertion-generator-v1.2.0/
├── backend/
│   ├── main.py              # FastAPI server
│   ├── rtl_parser.py        # RTL parsing
│   ├── llm_interface.py     # LLM API calls
│   ├── assertion_analyzer.py # Quality analysis
│   ├── testbench_generator.py
│   ├── example_designs.py   # 30+ examples
│   └── requirements.txt
├── frontend/
│   ├── src/
│   │   ├── App.jsx          # Main React app
│   │   ├── App.css          # Styles + syntax colors
│   │   ├── index.js
│   │   └── index.css
│   ├── public/
│   │   └── index.html
│   └── package.json
├── VERSION
└── README.md
```

## 🐛 Troubleshooting

### Grade shows N/A

This has been fixed in v1.2.0. If you still see N/A:
1. Make sure you're using the v1.2.0 files
2. Check that assertions were actually generated
3. Check browser console for errors

### Syntax highlighting not working

1. Ensure App.css is properly loaded
2. Check that the `SyntaxHighlighter` component is being used
3. Verify CSS classes match: `.token-keyword`, `.token-sva-keyword`, etc.

### API errors

1. Check backend is running on port 8000
2. Verify CORS is enabled
3. Check API keys if using LLM features

## 📄 License

MIT License - See LICENSE file for details.

## 🤝 Contributing

Contributions welcome! Please read the contributing guidelines first.

---

**RTL Assertion Generator v1.2.0** - Making formal verification accessible
