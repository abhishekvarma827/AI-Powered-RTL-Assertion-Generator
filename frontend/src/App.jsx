import React, { useState, useMemo } from 'react';
import axios from 'axios';
import './App.css';
import profileImage from './profile.png';

const VERSION = '9.3.1';
const API_BASE = 'https://ai-powered-rtl-assertion-generator.onrender.com';

// Category explanations
const CATEGORY_EXPLANATIONS = {
  timing: {
    icon: '⏱️',
    title: 'Timing Assertions',
    description: 'Verify timing relationships between signals',
    examples: [
      'Clock-to-output delays',
      'Setup and hold time checks',
      'Signal propagation delays',
      'Cycle-accurate behavior verification'
    ],
    keywords: ['posedge', 'negedge', '##', 'delay', 'cycle']
  },
  data_integrity: {
    icon: '🔒',
    title: 'Data Integrity Assertions',
    description: 'Ensure data values remain correct and consistent',
    examples: [
      'Data stability checks',
      'Value range validation',
      'Parity/checksum verification',
      'Data corruption detection'
    ],
    keywords: ['$stable', '$changed', 'data', 'value']
  },
  reset: {
    icon: '🔄',
    title: 'Reset Assertions',
    description: 'Verify proper reset behavior and initialization',
    examples: [
      'All registers initialize to known values',
      'Outputs go to safe state during reset',
      'Reset synchronization checks',
      'Reset release behavior'
    ],
    keywords: ['rst', 'reset', 'init', 'default']
  },
  coverage: {
    icon: '📊',
    title: 'Coverage Properties',
    description: 'Track functional coverage points reached during simulation',
    examples: [
      'State machine state coverage',
      'Signal toggle coverage',
      'Condition/branch coverage',
      'Cross-coverage of multiple signals'
    ],
    keywords: ['cover', 'coverpoint', 'bins']
  },
  sequence: {
    icon: '⚡',
    title: 'Sequence Assertions',
    description: 'Verify multi-cycle sequential behavior patterns',
    examples: [
      'Request-acknowledge handshakes',
      'Multi-cycle protocol sequences',
      'State transition sequences',
      'Pipelined operation verification'
    ],
    keywords: ['sequence', '|=>', '|->', 'throughout', 'within']
  },
  protocol: {
    icon: '🤝',
    title: 'Protocol Assertions',
    description: 'Verify communication protocol compliance',
    examples: [
      'Valid-ready handshaking',
      'Bus protocol compliance',
      'FIFO protocol rules',
      'Arbiter grant protocols'
    ],
    keywords: ['valid', 'ready', 'ack', 'req', 'grant']
  },
  clock: {
    icon: '⚡',
    title: 'Clock Assertions',
    description: 'Verify clock-related properties',
    examples: [
      'Clock frequency checks',
      'Clock gating verification',
      'Clock domain crossing',
      'Clock enable behavior'
    ],
    keywords: ['clk', 'clock', 'edge', 'frequency']
  },
  invariant: {
    icon: '⚡',
    title: 'Invariant Assertions',
    description: 'Properties that must always or never occur',
    examples: [
      'Mutual exclusion checks',
      'One-hot encoding validation',
      'Illegal state detection',
      'Safety property verification'
    ],
    keywords: ['always', 'never', 'eventually', '$onehot']
  }
};

// ALL RTL Example Categories with ALL Types
const EXAMPLE_CATEGORIES = {
  "Combinational Logic": {
    icon: "⚡",
    designs: {
      "Half Adder": {
        types: ["Behavioral", "Dataflow", "Structural"],
        keys: ["half_adder_behavioral", "half_adder_dataflow", "half_adder_structural"]
      },
      "Full Adder": {
        types: ["Behavioral", "Dataflow", "Structural"],
        keys: ["full_adder_behavioral", "full_adder_dataflow", "full_adder_structural"]
      },
      "2:1 MUX": {
        types: ["Behavioral", "Dataflow"],
        keys: ["mux_2to1_behavioral", "mux_2to1_dataflow"]
      },
      "4:1 MUX": {
        types: ["Behavioral", "Dataflow"],
        keys: ["mux_4to1_behavioral", "mux_4to1_dataflow"]
      },
      "1:2 DEMUX": {
        types: ["Behavioral"],
        keys: ["demux_1to2_behavioral"]
      },
      "1:4 DEMUX": {
        types: ["Behavioral", "Dataflow"],
        keys: ["demux_1to4_behavioral", "demux_1to4_dataflow"]
      }
    }
  },
  "Encoders & Decoders": {
    icon: "⚡",
    designs: {
      "4:2 Priority Encoder": {
        types: ["Behavioral"],
        keys: ["encoder_4to2"]
      },
      "8:3 Priority Encoder": {
        types: ["Behavioral"],
        keys: ["encoder_8to3"]
      },
      "2:4 Decoder": {
        types: ["Behavioral", "Dataflow"],
        keys: ["decoder_2to4_behavioral", "decoder_2to4_dataflow"]
      },
      "3:8 Decoder": {
        types: ["Behavioral"],
        keys: ["decoder_3to8"]
      }
    }
  },
  "Sequential Logic": {
    icon: "🔄",
    designs: {
      "Up Counter": {
        types: ["Behavioral"],
        keys: ["counter_up"]
      },
      "Down Counter": {
        types: ["Behavioral"],
        keys: ["counter_down"]
      },
      "Up/Down Counter": {
        types: ["Behavioral"],
        keys: ["counter_updown"]
      },
      "BCD Counter (Mod-10)": {
        types: ["Behavioral"],
        keys: ["counter_mod10"]
      },
      "Simple FSM": {
        types: ["Behavioral"],
        keys: ["fsm_simple"]
      }
    }
  },
  "Frequency Dividers": {
    icon: "⚡",
    designs: {
      "Divide by 2": {
        types: ["Behavioral"],
        keys: ["freq_div_by2"]
      },
      "Divide by N": {
        types: ["Parameterized"],
        keys: ["freq_div_by_n"]
      }
    }
  },
  "Comparators": {
    icon: "⚡",
    designs: {
      "1-bit Comparator": {
        types: ["Behavioral", "Dataflow"],
        keys: ["comparator_1bit_behavioral", "comparator_1bit_dataflow"]
      },
      "4-bit Comparator": {
        types: ["Behavioral"],
        keys: ["comparator_4bit"]
      },
      "N-bit Comparator": {
        types: ["Behavioral", "Dataflow"],
        keys: ["comparator_nbit_behavioral", "comparator_nbit_dataflow"]
      }
    }
  },
  "Memory & Buffers": {
    icon: "💾",
    designs: {
      "Sync FIFO": {
        types: ["Behavioral"],
        keys: ["fifo_sync"]
      },
      "Async FIFO": {
        types: ["Behavioral"],
        keys: ["fifo_async"]
      },
      "Register File": {
        types: ["Behavioral"],
        keys: ["register_file"]
      }
    }
  },
  "Shift Registers": {
    icon: "⚡",
    designs: {
      "SISO": {
        types: ["Behavioral"],
        keys: ["shift_reg_siso"]
      },
      "SIPO": {
        types: ["Behavioral"],
        keys: ["shift_reg_sipo"]
      },
      "PISO": {
        types: ["Behavioral"],
        keys: ["shift_reg_piso"]
      },
      "PIPO": {
        types: ["Behavioral"],
        keys: ["shift_reg_pipo"]
      }
    }
  },
  "Arithmetic Units": {
    icon: "⚡",
    designs: {
      "ALU (8-bit)": {
        types: ["Behavioral"],
        keys: ["alu_8bit"]
      },
      "Multiplier": {
        types: ["Behavioral"],
        keys: ["multiplier"]
      },
      "Divider": {
        types: ["Behavioral"],
        keys: ["divider"]
      }
    }
  }
};

// Syntax highlighting tokens
const SV_KEYWORDS = [
  'module', 'endmodule', 'input', 'output', 'inout', 'wire', 'reg', 'logic',
  'always', 'always_ff', 'always_comb', 'initial', 'begin', 'end',
  'if', 'else', 'case', 'endcase', 'for', 'while',
  'assign', 'parameter', 'localparam', 'posedge', 'negedge',
  'property', 'endproperty', 'sequence', 'endsequence',
  'disable', 'iff'
];

const SVA_KEYWORDS = [
  'assert', 'assume', 'cover', 'restrict', 'expect'
];

// Syntax highlighter component
const SyntaxHighlighter = ({ code }) => {
  const highlightCode = useMemo(() => {
    if (!code) return [];
    
    // Ensure we process the complete code by trimming only trailing whitespace
    const codeStr = String(code).trimEnd();
    const lines = codeStr.split('\n');
    
    return lines.map((line, lineIdx) => {
      const tokens = [];
      let remaining = line;
      let position = 0;
      
      while (remaining.length > 0) {
        let matched = false;
        
        // Comments
        const singleComment = remaining.match(/^(\/\/.*)/);
        if (singleComment) {
          tokens.push({ type: 'comment', text: singleComment[1] });
          remaining = '';
          matched = true;
        }
        
        // Strings
        if (!matched) {
          const stringMatch = remaining.match(/^("(?:[^"\\]|\\.)*")/);
          if (stringMatch) {
            tokens.push({ type: 'string', text: stringMatch[1] });
            remaining = remaining.slice(stringMatch[1].length);
            matched = true;
          }
        }
        
        // Numbers
        if (!matched) {
          const numMatch = remaining.match(/^(\d+'[bBhHdDoO][0-9a-fA-FxXzZ_]+|\d+)/);
          if (numMatch) {
            tokens.push({ type: 'number', text: numMatch[1] });
            remaining = remaining.slice(numMatch[1].length);
            matched = true;
          }
        }
        
        // SVA operators
        if (!matched) {
          const svaOpMatch = remaining.match(/^(\|\-\>|\|=\>|##\d*)/);
          if (svaOpMatch) {
            tokens.push({ type: 'sva-operator', text: svaOpMatch[1] });
            remaining = remaining.slice(svaOpMatch[1].length);
            matched = true;
          }
        }
        
        // System functions
        if (!matched) {
          const sysFuncMatch = remaining.match(/^(\$[a-zA-Z_][a-zA-Z0-9_]*)/);
          if (sysFuncMatch) {
            tokens.push({ type: 'system-function', text: sysFuncMatch[1] });
            remaining = remaining.slice(sysFuncMatch[1].length);
            matched = true;
          }
        }
        
        // Keywords and identifiers
        if (!matched) {
          const wordMatch = remaining.match(/^([a-zA-Z_][a-zA-Z0-9_]*)/);
          if (wordMatch) {
            const word = wordMatch[1];
            let tokenType = 'identifier';
            
            if (SVA_KEYWORDS.includes(word)) {
              tokenType = 'sva-keyword';
            } else if (SV_KEYWORDS.includes(word)) {
              tokenType = 'keyword';
            } else if (['clk', 'clock', 'rst', 'reset', 'rst_n'].includes(word.toLowerCase())) {
              tokenType = 'signal-clock';
            }
            
            tokens.push({ type: tokenType, text: word });
            remaining = remaining.slice(word.length);
            matched = true;
          }
        }
        
        // Operators
        if (!matched) {
          const opMatch = remaining.match(/^([<>=!&|^~+\-*/%]+|[{}()\[\];:,@#])/);
          if (opMatch) {
            tokens.push({ type: 'operator', text: opMatch[1] });
            remaining = remaining.slice(opMatch[1].length);
            matched = true;
          }
        }
        
        // Whitespace
        if (!matched) {
          const wsMatch = remaining.match(/^(\s+)/);
          if (wsMatch) {
            tokens.push({ type: 'whitespace', text: wsMatch[1] });
            remaining = remaining.slice(wsMatch[1].length);
            matched = true;
          }
        }
        
        // Fallback
        if (!matched && remaining.length > 0) {
          tokens.push({ type: 'text', text: remaining[0] });
          remaining = remaining.slice(1);
        }
        
        position++;
        if (position > 10000) break;
      }
      
      // Ensure empty lines have at least one token
      if (tokens.length === 0) {
        tokens.push({ type: 'whitespace', text: ' ' });
      }
      
      return { lineNum: lineIdx + 1, tokens };
    });
  }, [code]);
  
  return (
    <div className="syntax-highlighter">
      <div className="line-numbers">
        {highlightCode.map((line) => (
          <span key={line.lineNum} className="line-number">{line.lineNum}</span>
        ))}
      </div>
      <pre className="code-content">
        {highlightCode.map((line) => (
          <div key={line.lineNum} className="code-line">
            {line.tokens.map((token, idx) => (
              <span key={idx} className={`token-${token.type}`}>
                {token.text}
              </span>
            ))}
          </div>
        ))}
      </pre>
    </div>
  );
};

// Progress Bar Component
const ProgressBar = ({ isVisible, stage, progress, message }) => {
  if (!isVisible) return null;
  
  const getIcon = () => {
    switch(stage) {
      case 'loading': return '⏳';
      case 'parsing': return '🔍';
      case 'generating': return '⚡';
      case 'analyzing': return '📊';
      case 'testbench': return '🧪';
      case 'complete': return '✓';
      default: return '⚡';
    }
  };
  
  const getTitle = () => {
    switch(stage) {
      case 'loading': return 'Loading Example';
      case 'parsing': return 'Parsing RTL Code';
      case 'generating': return 'Generating Assertions';
      case 'analyzing': return 'Analyzing Quality';
      case 'testbench': return 'Generating Testbench';
      case 'complete': return 'Complete!';
      default: return 'Processing...';
    }
  };
  
  return (
    <div className="progress-overlay">
      <div className="progress-modal">
        <div className="progress-header">
          <span className="progress-icon">{getIcon()}</span>
          <span className="progress-stage">{getTitle()}</span>
        </div>
        <div className="progress-bar-container">
          <div 
            className="progress-bar-fill"
            style={{ width: `${progress}%` }}
          />
        </div>
        <div className="progress-message">{message}</div>
        <div className="progress-percentage">{progress}%</div>
      </div>
    </div>
  );
};

// Category Detail Modal
const CategoryDetailModal = ({ category, data, count, onClose }) => {
  if (!category || !data) return null;
  
  return (
    <div className="modal-overlay" onClick={onClose}>
      <div className="category-detail-modal" onClick={e => e.stopPropagation()}>
        <div className="modal-header">
          <h2>{data.icon} {data.title}</h2>
          <button className="modal-close" onClick={onClose}></button>
        </div>
        <div className="category-detail-content">
          <div className="category-count-badge">
            <span className="count-value">{count}</span>
            <span className="count-label">assertions found</span>
          </div>
          
          <div className="category-description">
            <p>{data.description}</p>
          </div>
          
          <div className="category-examples">
            <h4>What this category checks:</h4>
            <ul>
              {data.examples.map((example, idx) => (
                <li key={idx}>{example}</li>
              ))}
            </ul>
          </div>
          
          <div className="category-keywords">
            <h4>Keywords detected:</h4>
            <div className="keyword-chips">
              {data.keywords.map((kw, idx) => (
                <span key={idx} className="keyword-chip">{kw}</span>
              ))}
            </div>
          </div>
        </div>
      </div>
    </div>
  );
};

// Example Selector Modal
const ExampleSelectorModal = ({ isOpen, onClose, onSelect }) => {
  const [selectedCategory, setSelectedCategory] = useState(null);
  const [selectedDesign, setSelectedDesign] = useState(null);
  
  const handleTypeSelect = (key) => {
    onSelect(key);
    onClose();
    setSelectedCategory(null);
    setSelectedDesign(null);
  };
  
  if (!isOpen) return null;
  
  return (
    <div className="modal-overlay" onClick={onClose}>
      <div className="example-modal" onClick={e => e.stopPropagation()}>
        <div className="modal-header">
          <h2>📦 Load RTL Example</h2>
          <button className="modal-close" onClick={onClose}></button>
        </div>
        
        <div className="example-browser">
          <div className="browser-column">
            <h3>Category</h3>
            <div className="column-items">
              {Object.entries(EXAMPLE_CATEGORIES).map(([catName, catData]) => (
                <button
                  key={catName}
                  className={`column-item ${selectedCategory === catName ? 'selected' : ''}`}
                  onClick={() => {
                    setSelectedCategory(catName);
                    setSelectedDesign(null);
                  }}
                >
                  <span className="item-icon">{catData.icon}</span>
                  <span className="item-name">{catName}</span>
                </button>
              ))}
            </div>
          </div>
          
          <div className="browser-column">
            <h3>Design</h3>
            <div className="column-items">
              {selectedCategory && Object.entries(EXAMPLE_CATEGORIES[selectedCategory].designs).map(([designName, designData]) => (
                <button
                  key={designName}
                  className={`column-item ${selectedDesign === designName ? 'selected' : ''}`}
                  onClick={() => setSelectedDesign(designName)}
                >
                  <span className="item-name">{designName}</span>
                </button>
              ))}
              {!selectedCategory && (
                <div className="column-placeholder">📂 Select a category</div>
              )}
            </div>
          </div>
          
          <div className="browser-column">
            <h3>RTL Style</h3>
            <div className="column-items">
              {selectedCategory && selectedDesign && (
                EXAMPLE_CATEGORIES[selectedCategory].designs[selectedDesign].types.map((type, idx) => {
                  const key = EXAMPLE_CATEGORIES[selectedCategory].designs[selectedDesign].keys[idx];
                  return (
                    <button
                      key={type}
                      className="column-item type-item"
                      onClick={() => handleTypeSelect(key)}
                    >
                      <span className={`type-badge type-${type.toLowerCase()}`}>{type}</span>
                    </button>
                  );
                })
              )}
              {(!selectedCategory || !selectedDesign) && (
                <div className="column-placeholder">📄 Select a design</div>
              )}
            </div>
          </div>
        </div>
        
        <div className="quick-access">
          <h4>Quick Access</h4>
          <div className="quick-buttons">
            <button onClick={() => handleTypeSelect('full_adder_behavioral')}>Full Adder</button>
            <button onClick={() => handleTypeSelect('counter_up')}>Counter</button>
            <button onClick={() => handleTypeSelect('fsm_simple')}>FSM</button>
            <button onClick={() => handleTypeSelect('fifo_sync')}>FIFO</button>
            <button onClick={() => handleTypeSelect('alu_8bit')}>ALU</button>
            <button onClick={() => handleTypeSelect('shift_reg_sipo')}>Shift Reg</button>
          </div>
        </div>
      </div>
    </div>
  );
};

// Grade Display Component
const GradeDisplay = ({ grade, explanation, isExpanded, onToggle }) => {
  const gradeColors = {
    'A': { bg: '#10b981', text: '#ffffff', label: 'Excellent' },
    'B': { bg: '#3b82f6', text: '#ffffff', label: 'Good' },
    'C': { bg: '#f59e0b', text: '#000000', label: 'Adequate' },
    'D': { bg: '#f97316', text: '#ffffff', label: 'Needs Work' },
    'F': { bg: '#ef4444', text: '#ffffff', label: 'Poor' }
  };
  
  const gradeInfo = gradeColors[grade] || gradeColors['C'];
  
  return (
    <div className="grade-display-container">
      <button 
        className="grade-card"
        onClick={onToggle}
        style={{ '--grade-bg': gradeInfo.bg, '--grade-text': gradeInfo.text }}
      >
        <div className="grade-main">
          <span className="grade-letter">{grade || 'C'}</span>
          <span className="grade-label">{gradeInfo.label}</span>
        </div>
        <span className="grade-expand-icon">{isExpanded ? '▼' : '▶'}</span>
      </button>
      
      {isExpanded && explanation && (
        <div className="grade-explanation">
          <h4>Grading Criteria</h4>
          <div className="grade-breakdown">
            {explanation.criteria && Object.entries(explanation.criteria).map(([key, value]) => (
              <div key={key} className="criterion">
                <span className="criterion-name">{key.replace(/_/g, ' ')}</span>
                <span className="criterion-value">{typeof value === 'number' ? `${value}/10` : value}</span>
              </div>
            ))}
          </div>
          {explanation.summary && <p className="grade-summary">{explanation.summary}</p>}
        </div>
      )}
    </div>
  );
};

// Clickable Categories Component
const CategoriesDisplay = ({ categories, isExpanded, onToggle, onCategoryClick, activeCategory }) => {
  const [selectedCategory, setSelectedCategory] = useState(null);
  
  const handleCategoryClick = (cat) => {
    setSelectedCategory(cat);
    if (onCategoryClick) {
      onCategoryClick(cat);
    }
  };
  
  return (
    <>
      <div className="categories-section">
        <button className="section-toggle" onClick={onToggle}>
          <span>Categories</span>
          <span>{isExpanded ? '▼' : '▶'}</span>
        </button>
        {isExpanded && (
          <div className="categories-grid">
            {Object.entries(categories).map(([cat, count]) => {
              const catData = CATEGORY_EXPLANATIONS[cat] || {
                icon: '⚡',
                title: cat,
                description: `Assertions related to ${cat}`,
                examples: [],
                keywords: []
              };
              return (
                <button
                  key={cat}
                  className={`category-chip clickable ${activeCategory === cat ? 'active' : ''}`}
                  onClick={() => handleCategoryClick(cat)}
                  title="Click to filter assertions"
                >
                  <span className="category-icon">{catData.icon}</span>
                  <span className="category-name">{cat.replace(/_/g, ' ')}</span>
                  <span className="category-count">{count}</span>
                </button>
              );
            })}
          </div>
        )}
      </div>
      
      {/* Category Detail Modal */}
      {selectedCategory && (
        <CategoryDetailModal
          category={selectedCategory}
          data={CATEGORY_EXPLANATIONS[selectedCategory] || {
            icon: '⚡',
            title: selectedCategory,
            description: `Assertions related to ${selectedCategory}`,
            examples: ['Various checks in this category'],
            keywords: [selectedCategory]
          }}
          count={categories[selectedCategory]}
          onClose={() => setSelectedCategory(null)}
        />
      )}
    </>
  );
};

// Main App Component
function App() {
  const [rtlCode, setRtlCode] = useState('');
  const [moduleInfo, setModuleInfo] = useState(null);
  const [rtlExplanation, setRtlExplanation] = useState('');
  const [assertions, setAssertions] = useState('');
  const [analysis, setAnalysis] = useState(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState(null);
  const [selectedModel, setSelectedModel] = useState('gemini');
  const [theme, setTheme] = useState('dark');
  const [showExampleModal, setShowExampleModal] = useState(false);
  const [expandedSections, setExpandedSections] = useState({
    grade: false,
    categories: true,
    recommendations: false
  });
  const [editMode, setEditMode] = useState(false);
  const [editedAssertions, setEditedAssertions] = useState('');
  const [filteredCategory, setFilteredCategory] = useState(null);
  const [originalAssertions, setOriginalAssertions] = useState('');
  const [feedback, setFeedback] = useState('');
  const [feedbackLoading, setFeedbackLoading] = useState(false);
  
  // Progress state
  const [progressState, setProgressState] = useState({
    visible: false,
    stage: '',
    percent: 0,
    message: ''
  });

  const showProgress = (stage, percent, message) => {
    setProgressState({
      visible: true,
      stage,
      percent,
      message
    });
  };

  const hideProgress = () => {
    setProgressState(prev => ({ ...prev, visible: false }));
  };

  const toggleSection = (section) => {
    setExpandedSections(prev => ({ ...prev, [section]: !prev[section] }));
  };

  // Handle category filtering
  const handleCategoryFilter = (category) => {
    if (filteredCategory === category) {
      // Toggle off - show all assertions
      setFilteredCategory(null);
      setAssertions(originalAssertions);
    } else {
      // Filter to show only selected category
      setFilteredCategory(category);
      const filtered = filterAssertionsByCategory(originalAssertions, category);
      setAssertions(filtered);
    }
  };

  // Filter assertions by category
  const filterAssertionsByCategory = (assertionsText, category) => {
    if (!assertionsText || !category) return assertionsText;
    
    const lines = assertionsText.split('\n');
    const filteredLines = [];
    let inTargetSection = false;
    let sectionDepth = 0;
    
    // Always include module header and footer
    const moduleHeaderLines = [];
    const moduleFooterLines = [];
    let foundModule = false;
    
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      const trimmedLine = line.trim();
      
      // Capture module header (everything before first assertion/property)
      if (!foundModule && (trimmedLine.startsWith('module ') || trimmedLine.includes('```systemverilog'))) {
        moduleHeaderLines.push(line);
        continue;
      }
      
      if (!foundModule && !trimmedLine.startsWith('//') && !trimmedLine.includes('property') && 
          !trimmedLine.includes('assert') && !trimmedLine.includes('cover') && trimmedLine) {
        moduleHeaderLines.push(line);
        continue;
      }
      
      if (trimmedLine.startsWith('//') || trimmedLine.includes('property') || 
          trimmedLine.includes('assert') || trimmedLine.includes('cover')) {
        foundModule = true;
      }
      
      // Capture endmodule and closing markers
      if (trimmedLine === 'endmodule' || trimmedLine === '```') {
        moduleFooterLines.push(line);
        continue;
      }
      
      // Check for category section start (comments with category name)
      const categoryNameNormalized = category.toLowerCase().replace(/_/g, ' ');
      const lineNormalized = trimmedLine.toLowerCase();
      
      if (trimmedLine.startsWith('//') && lineNormalized.includes(categoryNameNormalized)) {
        inTargetSection = true;
        filteredLines.push(line);
        continue;
      }
      
      // Check if we've entered a different category section
      if (trimmedLine.startsWith('//') && trimmedLine.length > 5) {
        const isOtherCategory = Object.keys(CATEGORY_EXPLANATIONS).some(cat => {
          if (cat === category) return false;
          const otherCatName = cat.toLowerCase().replace(/_/g, ' ');
          return lineNormalized.includes(otherCatName);
        });
        
        if (isOtherCategory) {
          inTargetSection = false;
          continue;
        }
      }
      
      // Include lines in the target section
      if (inTargetSection) {
        filteredLines.push(line);
        
        // Track property/assertion blocks
        if (trimmedLine.includes('property') || trimmedLine.includes('assert') || trimmedLine.includes('cover')) {
          sectionDepth++;
        }
        if (trimmedLine.includes('endproperty') || trimmedLine.includes(';')) {
          // Continue capturing until we hit the next section
        }
      }
    }
    
    // Combine module header + filtered content + module footer
    if (filteredLines.length > 0) {
      return [...moduleHeaderLines, ...filteredLines, ...moduleFooterLines].join('\n');
    }
    
    return assertionsText;
  };

  // Load example
  const handleLoadExample = async (exampleName) => {
    setLoading(true);
    setError(null);
    showProgress('loading', 20, 'Fetching example design...');
    
    try {
      await new Promise(r => setTimeout(r, 200));
      showProgress('loading', 50, 'Loading RTL code...');
      
      const response = await axios.get(`${API_BASE}/examples/${exampleName}`);
      
      showProgress('loading', 100, 'Example loaded!');
      setRtlCode(response.data.code);
      setModuleInfo(null);
      setAssertions('');
      setAnalysis(null);
      
      setTimeout(hideProgress, 500);
    } catch (err) {
      setError(`Failed to load example: ${err.message}`);
      hideProgress();
    } finally {
      setLoading(false);
    }
  };

  // Parse RTL
  const handleParseRTL = async () => {
    if (!rtlCode.trim()) return;
    
    setLoading(true);
    setError(null);
    showProgress('parsing', 10, 'Initializing RTL parser...');
    
    try {
      await new Promise(r => setTimeout(r, 300));
      showProgress('parsing', 30, 'Extracting module declaration...');
      
      await new Promise(r => setTimeout(r, 300));
      showProgress('parsing', 50, 'Analyzing port definitions...');
      
      await new Promise(r => setTimeout(r, 300));
      showProgress('parsing', 70, 'Identifying internal signals...');
      
      const response = await axios.post(`${API_BASE}/parse-rtl`, { code: rtlCode });
      
      showProgress('parsing', 90, 'Inferring signal types...');
      await new Promise(r => setTimeout(r, 200));
      
      showProgress('complete', 100, 'RTL parsing complete!');
      setModuleInfo(response.data);
      
      // Generate explanation
      generateRTLExplanation(response.data);
      
      setTimeout(hideProgress, 800);
    } catch (err) {
      setError(`Parse error: ${err.response?.data?.detail || err.message}`);
      hideProgress();
    } finally {
      setLoading(false);
    }
  };

  // Generate RTL Explanation
  const generateRTLExplanation = (modInfo) => {
    const moduleName = modInfo.name;
    const ports = modInfo.ports || [];
    const parameters = modInfo.parameters || [];
    
    // Categorize ports
    const inputs = ports.filter(p => p.direction === 'input');
    const outputs = ports.filter(p => p.direction === 'output');
    const inouts = ports.filter(p => p.direction === 'inout');
    
    // Identify special signals
    const clocks = ports.filter(p => p.semantic_type === 'clock');
    const resets = ports.filter(p => p.semantic_type === 'reset');
    const controlSignals = ports.filter(p => p.semantic_type === 'control');
    const dataSignals = ports.filter(p => p.semantic_type === 'data');
    
    let explanation = ``;
    
    // Purpose inference based on name
    const nameLower = moduleName.toLowerCase();
    if (nameLower.includes('adder')) {
      explanation += `This is an adder circuit that performs arithmetic addition operations. `;
    } else if (nameLower.includes('multiplier') || nameLower.includes('mult')) {
      explanation += `This is a multiplier circuit that performs multiplication operations. `;
    } else if (nameLower.includes('counter')) {
      explanation += `This is a counter module that increments or decrements values based on clock cycles. `;
    } else if (nameLower.includes('fifo')) {
      explanation += `This is a FIFO (First-In-First-Out) buffer that manages data flow between different clock domains or processing speeds. `;
    } else if (nameLower.includes('mux') || nameLower.includes('multiplexer')) {
      explanation += `This is a multiplexer that selects one input from multiple sources based on control signals. `;
    } else if (nameLower.includes('decoder')) {
      explanation += `This is a decoder that converts encoded inputs into multiple output signals. `;
    } else if (nameLower.includes('encoder')) {
      explanation += `This is an encoder that converts multiple inputs into an encoded output. `;
    } else if (nameLower.includes('fsm') || nameLower.includes('state')) {
      explanation += `This is a finite state machine (FSM) that implements sequential logic with different operational states. `;
    } else if (nameLower.includes('alu')) {
      explanation += `This is an Arithmetic Logic Unit (ALU) that performs arithmetic and logical operations. `;
    } else if (nameLower.includes('reg') && !nameLower.includes('register_file')) {
      explanation += `This is a register module for storing and managing data. `;
    } else if (nameLower.includes('comparator')) {
      explanation += `This is a comparator that compares input values and generates comparison results. `;
    } else {
      explanation += `This module implements digital logic functionality. `;
    }
    
    // Interface description
    explanation += `The module has ${ports.length} ports (${inputs.length} input${inputs.length !== 1 ? 's' : ''}, ${outputs.length} output${outputs.length !== 1 ? 's' : ''}`;
    if (inouts.length > 0) explanation += `, ${inouts.length} inout${inouts.length !== 1 ? 's' : ''}`;
    explanation += `). `;
    
    // Clock and Reset
    if (clocks.length > 0) {
      explanation += `It operates on ${clocks.length} clock signal${clocks.length !== 1 ? 's' : ''} (${clocks.map(c => c.name).join(', ')}). `;
    }
    if (resets.length > 0) {
      const resetNames = resets.map(r => r.name);
      const hasActiveLow = resets.some(r => r.name.toLowerCase().includes('n') || r.name.toLowerCase().includes('_n'));
      explanation += `Reset is provided via ${resetNames.join(', ')} (${hasActiveLow ? 'active-low' : 'active-high'}). `;
    }
    
    // Data signals info
    const wideDataSignals = dataSignals.filter(s => {
      const width = s.width;
      if (!width || width === '1') return false;
      return true;
    });
    
    if (wideDataSignals.length > 0) {
      const widths = wideDataSignals.slice(0, 2).map(s => `${s.name} (${s.width} bits)`).join(', ');
      explanation += `Key data signals include ${widths}. `;
    }
    
    // Functionality hint
    if (controlSignals.length > 0) {
      explanation += `Control signals like ${controlSignals.slice(0, 3).map(s => s.name).join(', ')} manage the module's behavior. `;
    }
    
    setRtlExplanation(explanation.trim());
  };

  // Generate assertions
  const handleGenerateAssertions = async () => {
    if (!moduleInfo) return;
    
    setLoading(true);
    setError(null);
    showProgress('generating', 5, 'Preparing request...');
    
    try {
      await new Promise(r => setTimeout(r, 400));
      showProgress('generating', 10, `Connecting to ${selectedModel === 'claude' ? 'Claude Sonnet 4' : 'Google Gemini'}...`);
      
      await new Promise(r => setTimeout(r, 500));
      showProgress('generating', 20, 'Sending RTL code to LLM...');
      
      await new Promise(r => setTimeout(r, 600));
      showProgress('generating', 30, 'LLM analyzing module structure...');
      
      await new Promise(r => setTimeout(r, 500));
      showProgress('generating', 40, 'Generating reset behavior assertions...');
      
      await new Promise(r => setTimeout(r, 500));
      showProgress('generating', 50, 'Creating timing property checks...');
      
      await new Promise(r => setTimeout(r, 500));
      showProgress('generating', 60, 'Adding data integrity assertions...');
      
      const responsePromise = axios.post(`${API_BASE}/generate-assertions`, {
        code: rtlCode,
        module_info: moduleInfo,
        model: selectedModel
      });
      
      showProgress('generating', 70, 'Waiting for LLM response...');
      
      const response = await responsePromise;
      
      showProgress('analyzing', 80, 'Assertions received! Analyzing quality...');
      await new Promise(r => setTimeout(r, 400));
      
      showProgress('analyzing', 90, 'Calculating coverage and grade...');
      await new Promise(r => setTimeout(r, 300));
      
      setAssertions(response.data.assertions);
      setOriginalAssertions(response.data.assertions);
      setEditedAssertions(response.data.assertions);
      setFilteredCategory(null);
      
      // Process analysis with guaranteed grade
      if (response.data.analysis) {
        const analysisData = response.data.analysis;
        let grade = analysisData.grade || analysisData.quality_grade;
        
        if (!grade || grade === 'N/A') {
          const coverage = analysisData.coverage_percentage || 0;
          if (coverage >= 90) grade = 'A';
          else if (coverage >= 75) grade = 'B';
          else if (coverage >= 60) grade = 'C';
          else if (coverage >= 40) grade = 'D';
          else grade = 'F';
        }
        
        setAnalysis({
          ...analysisData,
          grade: grade,
          grade_explanation: analysisData.grade_explanation || {
            criteria: {
              coverage: Math.min(10, Math.round((analysisData.coverage_percentage || 0) / 10)),
              completeness: analysisData.categories ? Math.min(10, Object.keys(analysisData.categories).length * 2) : 5,
              quality: grade === 'A' ? 10 : grade === 'B' ? 8 : grade === 'C' ? 6 : grade === 'D' ? 4 : 2
            },
            summary: `Generated ${analysisData.total_assertions || 0} assertions with ${analysisData.coverage_percentage || 0}% coverage`
          }
        });
      }
      
      showProgress('complete', 100, 'Assertion generation complete!');
      setTimeout(hideProgress, 1000);
      
    } catch (err) {
      setError(`Generation error: ${err.response?.data?.detail || err.message}`);
      hideProgress();
    } finally {
      setLoading(false);
    }
  };

  // Generate testbench
  const handleGenerateTestbench = async (type = 'simple') => {
    if (!assertions || !moduleInfo) return;
    
    setLoading(true);
    setError(null);
    showProgress('testbench', 20, `Creating ${type} testbench...`);
    
    try {
      await new Promise(r => setTimeout(r, 300));
      showProgress('testbench', 40, 'Generating clock and reset logic...');
      
      await new Promise(r => setTimeout(r, 300));
      showProgress('testbench', 60, 'Adding stimulus generation...');
      
      const response = await axios.post(`${API_BASE}/generate-testbench`, {
        module_info: moduleInfo,
        assertions: editMode ? editedAssertions : assertions,
        type: type
      });
      
      showProgress('testbench', 80, 'Finalizing testbench...');
      await new Promise(r => setTimeout(r, 200));
      
      showProgress('complete', 100, 'Testbench generated!');
      
      // Download the testbench
      const blob = new Blob([response.data.testbench], { type: 'text/plain' });
      const url = URL.createObjectURL(blob);
      const a = document.createElement('a');
      a.href = url;
      a.download = `${moduleInfo.name}_tb.sv`;
      a.click();
      URL.revokeObjectURL(url);
      
      setTimeout(hideProgress, 800);
    } catch (err) {
      setError(`Testbench error: ${err.response?.data?.detail || err.message}`);
      hideProgress();
    } finally {
      setLoading(false);
    }
  };

  // Export

  // Get AI Feedback
  const handleGetFeedback = async () => {
    if (!rtlCode || !moduleInfo) {
      setError('Please parse RTL code first');
      return;
    }

    setFeedbackLoading(true);
    setError(null);

    try {
      const response = await axios.post(`${API_BASE}/get-feedback`, {
        code: rtlCode,
        module_info: moduleInfo,
        assertions: assertions || null,
        model: selectedModel
      });

      setFeedback(response.data.feedback);
    } catch (err) {
      console.error('Feedback error:', err);
      setError(err.response?.data?.detail || 'Failed to generate feedback. Please check your API configuration.');
    } finally {
      setFeedbackLoading(false);
    }
  };
  const handleExport = async (format) => {
    if (!assertions) return;
    try {
      const response = await axios.post(`${API_BASE}/export`, {
        assertions: editMode ? editedAssertions : assertions,
        module_name: moduleInfo?.name || 'module',
        format: format,
        analysis: analysis
      });
      
      const blob = new Blob([response.data.content], { type: 'text/plain' });
      const url = URL.createObjectURL(blob);
      const a = document.createElement('a');
      a.href = url;
      a.download = response.data.filename;
      a.click();
      URL.revokeObjectURL(url);
    } catch (err) {
      setError(`Export error: ${err.message}`);
    }
  };

  const getPortColor = (direction) => {
    const colors = { 'input': '#3b82f6', 'output': '#10b981', 'inout': '#f59e0b' };
    return colors[direction] || '#6b7280';
  };

  return (
    <div className={`app ${theme}`}>
      {/* Progress Bar */}
      <ProgressBar 
        isVisible={progressState.visible}
        stage={progressState.stage}
        progress={progressState.percent}
        message={progressState.message}
      />
      
      <header className="app-header">
        <div className="header-left">
          <h1>⚡ RTL Assertion Generator</h1>
          <span className="version-badge">v{VERSION}</span>
        </div>
        
        <div className="header-right">
          <a 
            href="mailto:avarma10@hawk.illinoistech.edu" 
            className="header-btn email-btn"
            title="Send me an email"
          >
            <svg viewBox="0 0 24 24" width="18" height="18" fill="currentColor">
              <path d="M20 4H4c-1.1 0-1.99.9-1.99 2L2 18c0 1.1.9 2 2 2h16c1.1 0 2-.9 2-2V6c0-1.1-.9-2-2-2zm0 4l-8 5-8-5V6l8 5 8-5v2z"/>
            </svg>
            <span>Email</span>
          </a>
          <a 
            href="https://buymeacoffee.com/avarma" 
            target="_blank" 
            rel="noopener noreferrer"
            className="header-btn coffee-btn"
            title="Buy me a coffee"
          >
            <svg viewBox="0 0 24 24" width="18" height="18" fill="currentColor">
              <path d="M2 21h18v-2H2v2zm1-5h16c.55 0 1-.45 1-1V7c0-.55-.45-1-1-1H3c-.55 0-1 .45-1 1v8c0 .55.45 1 1 1zm15-3c.55 0 1-.45 1-1s-.45-1-1-1-1 .45-1 1 .45 1 1 1zM3 4V2h18v2H3z"/>
            </svg>
            <span>Buy me a coffee</span>
          </a>
          <button className="theme-toggle" onClick={() => setTheme(t => t === 'dark' ? 'light' : 'dark')}>
            {theme === 'dark' ? '☀️' : '🌙'}
          </button>
        </div>
      </header>
      
      <main className="main-container">
        {/* Left Panel */}
        <div className="panel input-panel">
          <div className="panel-header">
            <h2>RTL Code Input</h2>
            <button className="btn btn-secondary" onClick={() => setShowExampleModal(true)} disabled={loading}>
              📦 Load Example
            </button>
          </div>
          
          <div className="code-input-wrapper">
            {rtlCode.trim() ? (
              <SyntaxHighlighter code={rtlCode} />
            ) : (
              <textarea
                className="code-input"
                value={rtlCode}
                onChange={(e) => setRtlCode(e.target.value)}
                placeholder="Paste your Verilog/SystemVerilog RTL code here..."
                disabled={loading}
                spellCheck="false"
              />
            )}
          </div>
          
          {rtlCode.trim() && (
            <div className="edit-rtl-controls">
              <button 
                className="btn btn-sm" 
                onClick={() => setRtlCode('')}
              >
                ✏️ Edit Code
              </button>
            </div>
          )}
          
          <div className="controls">
            <div className="control-row">
              <button className="btn btn-primary" onClick={handleParseRTL} disabled={loading || !rtlCode.trim()}>
                🔍 Parse RTL
              </button>
              
              <div className="model-select">
                <label>Model:</label>
                <select value={selectedModel} onChange={(e) => setSelectedModel(e.target.value)} disabled={loading}>
                  <option value="claude">Claude Sonnet 4</option>
                  <option value="gemini">Google Gemini 2.0</option>
                </select>
              </div>
            </div>
            
            <button className="btn btn-primary btn-generate" onClick={handleGenerateAssertions} disabled={loading || !moduleInfo}>
              ⚡ Generate Assertions
            </button>
          </div>
          
          {moduleInfo && (
            <div className="module-info">
              <h3>📦 Module: {moduleInfo.name}</h3>
              
              {rtlExplanation && (
                <div className="rtl-explanation">
                  <div className="explanation-header">
                    <span className="explanation-icon">💡</span>
                    <span className="explanation-title">What does this module do?</span>
                  </div>
                  <p className="explanation-text">{rtlExplanation}</p>
                </div>
              )}
              
              <div className="ports-section">
                <h4>Port Interface:</h4>
                <div className="ports-grid">
                  {moduleInfo.ports?.map((port, idx) => (
                    <div key={idx} className="port-chip" style={{ '--port-color': getPortColor(port.direction) }}>
                      <span className="port-direction">{port.direction}</span>
                      <span className="port-name">{port.name}</span>
                      {port.width && port.width !== '1' && (
                        <span className="port-width">[{port.width}]</span>
                      )}
                    </div>
                  ))}
                </div>
              </div>
            </div>
          )}
        </div>
        
        {/* Right Panel */}
        <div className="panel results-panel">
          <div className="panel-header">
            <h2>Generated Assertions</h2>
            {assertions && (
              <div className="panel-actions">
                <button className={`btn btn-sm ${editMode ? 'btn-active' : ''}`} onClick={() => { setEditMode(!editMode); if (!editMode) setEditedAssertions(assertions); }}>
                  ✏️ {editMode ? 'View' : 'Edit'}
                </button>
                <div className="export-dropdown">
                  <button className="btn btn-sm">💾 Export</button>
                  <div className="dropdown-content">
                    <button onClick={() => handleExport('sv')}>.sv file</button>
                    <button onClick={() => handleExport('txt')}>.txt file</button>
                    <button onClick={() => handleExport('json')}>.json file</button>
                  </div>
                </div>
              </div>
            )}
          </div>
          
          {error && <div className="error-message">⚠️ {error}</div>}
          
          {assertions ? (
            <div className="results-content">
              {analysis && (
                <div className="analysis-section">
                  <div className="analysis-header">
                    <GradeDisplay 
                      grade={analysis.grade}
                      explanation={analysis.grade_explanation}
                      isExpanded={expandedSections.grade}
                      onToggle={() => toggleSection('grade')}
                    />
                    
                    <div className="metric-card">
                      <div className="metric-icon">📊</div>
                      <div className="metric-content">
                        <div className="metric-value">{analysis.coverage_percentage || 0}%</div>
                        <div className="metric-label">Coverage</div>
                      </div>
                    </div>
                    
                    <div className="metric-card">
                      <div className="metric-icon">✓</div>
                      <div className="metric-content">
                        <div className="metric-value">{analysis.total_assertions || 0}</div>
                        <div className="metric-label">Assertions</div>
                      </div>
                    </div>
                    
                    <div className="metric-card">
                      <div className="metric-icon">📊</div>
                      <div className="metric-content">
                        <div className="metric-value">{Object.keys(analysis.categories || {}).length}</div>
                        <div className="metric-label">Categories</div>
                      </div>
                    </div>
                    
                    <div className="metric-card">
                      <div className="metric-icon">✓</div>
                      <div className="metric-content">
                        <div className="metric-value">{selectedModel === 'claude' ? 'Claude' : 'Gemini'}</div>
                        <div className="metric-label">Model</div>
                      </div>
                    </div>
                  </div>
                  
                  {/* Clickable Categories */}
                  {analysis.categories && (
                    <CategoriesDisplay
                      categories={analysis.categories}
                      isExpanded={expandedSections.categories}
                      onToggle={() => toggleSection('categories')}
                      onCategoryClick={handleCategoryFilter}
                      activeCategory={filteredCategory}
                    />
                  )}
                </div>
              )}
              
              <div className="assertions-code">
                {editMode ? (
                  <textarea className="code-editor" value={editedAssertions} onChange={(e) => setEditedAssertions(e.target.value)} spellCheck="false" />
                ) : (
                  <SyntaxHighlighter code={assertions} />
                )}
              </div>
              
              {/* Generate Testbench Buttons */}
              <div className="testbench-actions">
                <span className="testbench-label">🧪 Generate Testbench:</span>
                <button 
                  className="btn btn-sm btn-testbench"
                  onClick={() => handleGenerateTestbench('simple')}
                  disabled={loading}
                >
                  Simple
                </button>
                <button 
                  className="btn btn-sm btn-testbench"
                  onClick={() => handleGenerateTestbench('comprehensive')}
                  disabled={loading}
                >
                  Comprehensive
                </button>
              </div>
              
              {/* RTL Feedback Section */}
              <div className="feedback-section">
                <div className="feedback-header">
                  <span className="feedback-title">🤖 LLM Feedback</span>
                  <button 
                    className="btn btn-sm btn-feedback"
                    onClick={handleGetFeedback}
                    disabled={feedbackLoading || !rtlCode}
                  >
                    {feedbackLoading ? '⏳ Analyzing...' : '🔍 Get Feedback'}
                  </button>
                </div>
                
                {feedback && (
                  <div className="feedback-content">
                    <pre className="feedback-text">{feedback}</pre>
                  </div>
                )}
                
                {!feedback && !feedbackLoading && (
                  <div className="feedback-empty">
                    <p>Click "Get Feedback" to receive AI-powered analysis of your RTL code and generated assertions.</p>
                  </div>
                )}
              </div>
            </div>
          ) : (
            <div className="empty-state">
              <div className="empty-icon">📝</div>
              <h3>No Assertions Yet</h3>
              <p>Parse your RTL code and generate assertions to see results here.</p>
            </div>
          )}
        </div>
        
        {/* Creator Sidebar */}
        <aside className="creator-sidebar">
          <div className="creator-card-sidebar">
            <img src={profileImage} alt="Abhishek Varma" className="creator-avatar-sidebar" />
            <h3 className="creator-name-sidebar">Abhishek Varma</h3>
            <p className="creator-education-sidebar">MS in VLSI & Microelectronics</p>
            <p className="creator-university-sidebar">Illinois Institute of Technology</p>
            <p className="creator-bio-sidebar">
              Design & Verification Engineer with hands-on experience in building UVM environments, 
              debugging complex testbenches, and verifying AMBA-based IPs including AHB-to-APB bridges 
              and packet-based routers. Skilled in SystemVerilog, Verilog, UVM, functional coverage, 
              assertions, and regression automation using QuestaSim, Xcelium, Vivado, and HSPICE. 
              This tool automates SystemVerilog assertion generation using AI, streamlining RTL 
              verification workflows. Seeking full-time opportunities in Design and Verification.
            </p>
            <div className="creator-actions-sidebar">
              <a 
                href="https://www.linkedin.com/in/abhishek-varma-01317415b/" 
                target="_blank" 
                rel="noopener noreferrer"
                className="sidebar-btn linkedin-btn"
              >
                <svg viewBox="0 0 24 24" width="20" height="20" fill="currentColor">
                  <path d="M19 0h-14c-2.761 0-5 2.239-5 5v14c0 2.761 2.239 5 5 5h14c2.762 0 5-2.239 5-5v-14c0-2.761-2.238-5-5-5zm-11 19h-3v-11h3v11zm-1.5-12.268c-.966 0-1.75-.79-1.75-1.764s.784-1.764 1.75-1.764 1.75.79 1.75 1.764-.783 1.764-1.75 1.764zm13.5 12.268h-3v-5.604c0-3.368-4-3.113-4 0v5.604h-3v-11h3v1.765c1.396-2.586 7-2.777 7 2.476v6.759z"/>
                </svg>
                LinkedIn
              </a>
              <a 
                href="mailto:avarma10@hawk.illinoistech.edu" 
                className="sidebar-btn email-btn-sidebar"
              >
                <svg viewBox="0 0 24 24" width="20" height="20" fill="currentColor">
                  <path d="M20 4H4c-1.1 0-1.99.9-1.99 2L2 18c0 1.1.9 2 2 2h16c1.1 0 2-.9 2-2V6c0-1.1-.9-2-2-2zm0 4l-8 5-8-5V6l8 5 8-5v2z"/>
                </svg>
                Email
              </a>
              <a 
                href="https://buymeacoffee.com/avarma" 
                target="_blank" 
                rel="noopener noreferrer"
                className="sidebar-btn coffee-btn-sidebar"
              >
                <svg viewBox="0 0 24 24" width="20" height="20" fill="currentColor">
                  <path d="M2 21h18v-2H2v2zm1-5h16c.55 0 1-.45 1-1V7c0-.55-.45-1-1-1H3c-.55 0-1 .45-1 1v8c0 .55.45 1 1 1zm15-3c.55 0 1-.45 1-1s-.45-1-1-1-1 .45-1 1 .45 1 1 1zM3 4V2h18v2H3z"/>
                </svg>
                Buy me a coffee
              </a>
            </div>
          </div>
        </aside>
      </main>
      
      <ExampleSelectorModal isOpen={showExampleModal} onClose={() => setShowExampleModal(false)} onSelect={handleLoadExample} />
      
      <footer className="app-footer">
        <div className="footer-simple">
          <p> 2025 RTL Assertion Generator v{VERSION} | Automating SystemVerilog assertion generation with AI</p>
          <div className="footer-links">
            <a 
              href="https://www.linkedin.com/in/abhishek-varma-01317415b/" 
              target="_blank" 
              rel="noopener noreferrer"
            >
              LinkedIn
            </a>
            <span className="separator"></span>
            <a 
              href="mailto:avarma10@hawk.illinoistech.edu"
            >
              Contact
            </a>
            <span className="separator"></span>
            <a 
              href="https://buymeacoffee.com/avarma" 
              target="_blank" 
              rel="noopener noreferrer"
            >
              Support
            </a>
          </div>
        </div>
      </footer>
    </div>
  );
}

export default App;
