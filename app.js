/**
 * CFG Epsilon-Production Remover
 * Theory of Computation / Compiler Design Interactive Engine
 */

// 1. GRAMMAR PARSER & TOKENS

// 2. PARSER MODULE
class CFGParser {
  static isEpsilon(token) {
    if (token === null || token === undefined) return true;
    const t = token.trim();
    if (t === '') return true;
    const low = t.toLowerCase();
    return (
      low === 'eps' ||
      low === 'epsilon' ||
      low === 'e' ||
      low === 'ε' ||
      low === 'λ' ||
      low === 'lambda' ||
      low === '^'
    );
  }

  static parse(inputText) {
    const lines = inputText.split(/\r?\n/);
    const variableSet = new Set();
    let startSymbol = null;
    const rawRules = [];

    // First pass: extract all LHS variables & start symbol
    for (let i = 0; i < lines.length; i++) {
      let line = lines[i].trim();
      if (!line || line.startsWith('#') || line.startsWith('//')) continue;

      const arrowMatch = line.match(/\s*(->|→|::=)\s*/);
      if (!arrowMatch) continue;

      const lhs = line.substring(0, arrowMatch.index).trim();
      if (lhs) {
        variableSet.add(lhs);
        if (!startSymbol) startSymbol = lhs;
      }
    }

    if (variableSet.size === 0) {
      throw new Error("No valid production rules found. Rules must follow the format 'LHS -> alt1 | alt2'.");
    }

    // Second pass: tokenize alternatives
    for (let lineIndex = 0; lineIndex < lines.length; lineIndex++) {
      let line = lines[lineIndex].trim();
      if (!line || line.startsWith('#') || line.startsWith('//')) continue;

      const arrowMatch = line.match(/\s*(->|→|::=)\s*/);
      if (!arrowMatch) {
        throw new Error(`Line ${lineIndex + 1} is missing an arrow ('->', '→', or '::='): "${line}"`);
      }

      const lhs = line.substring(0, arrowMatch.index).trim();
      const rhsString = line.substring(arrowMatch.index + arrowMatch[0].length);

      if (!lhs) {
        throw new Error(`Line ${lineIndex + 1} has an empty Left-Hand Side (LHS).`);
      }

      const alternates = rhsString.split('|');
      for (let rawAlt of alternates) {
        const alt = rawAlt.trim();

        if (this.isEpsilon(alt)) {
          rawRules.push({
            lhs,
            rhsTokens: [],
            isEpsilon: true,
            rawAlt: alt || 'ε',
            lineNum: lineIndex + 1
          });
        } else {
          // Tokenize RHS
          let tokens = [];
          if (/\s+/.test(alt)) {
            tokens = alt.split(/\s+/).filter(t => t.length > 0);
          } else {
            // Intelligent tokenizer for unspaced symbols (e.g. 'aA', 'ABC', 'E\'')
            let i = 0;
            while (i < alt.length) {
              let matchedVar = null;
              for (let v of variableSet) {
                if (alt.startsWith(v, i)) {
                  if (!matchedVar || v.length > matchedVar.length) {
                    matchedVar = v;
                  }
                }
              }

              if (matchedVar) {
                tokens.push(matchedVar);
                i += matchedVar.length;
              } else {
                tokens.push(alt[i]);
                i++;
              }
            }
          }

          if (tokens.length === 1 && this.isEpsilon(tokens[0])) {
            rawRules.push({
              lhs,
              rhsTokens: [],
              isEpsilon: true,
              rawAlt: tokens[0],
              lineNum: lineIndex + 1
            });
          } else {
            rawRules.push({
              lhs,
              rhsTokens: tokens,
              isEpsilon: false,
              rawAlt: alt,
              lineNum: lineIndex + 1
            });
          }
        }
      }
    }

    // Determine terminal set
    const terminalSet = new Set();
    for (let r of rawRules) {
      if (!r.isEpsilon) {
        for (let tok of r.rhsTokens) {
          if (!variableSet.has(tok)) {
            terminalSet.add(tok);
          }
        }
      }
    }

    return {
      variables: Array.from(variableSet),
      terminals: Array.from(terminalSet),
      startSymbol,
      rules: rawRules
    };
  }
}

// 3. NULLABLE ENGINE (Two-phase fixed-point analysis)
class NullableEngine {
  static compute(variables, rules) {
    const nullableSet = new Set();
    const phase1Logs = [];
    const phase2Passes = [];

    // Phase 1: Direct epsilon productions (A -> ε)
    for (let r of rules) {
      if (r.isEpsilon) {
        if (!nullableSet.has(r.lhs)) {
          nullableSet.add(r.lhs);
          phase1Logs.push({
            variable: r.lhs,
            rule: `${r.lhs} -> ε`,
            reason: `Direct ε-production detected: variable ${r.lhs} produces empty string in 1 step.`
          });
        }
      }
    }

    // Phase 2: Iterative propagation (B -> X1...Xk where all Xi are nullable)
    let passNumber = 1;
    let changed = true;

    while (changed) {
      changed = false;
      const currentPassDiscoveries = [];

      for (let r of rules) {
        if (nullableSet.has(r.lhs) || r.isEpsilon) continue;

        if (r.rhsTokens.length > 0) {
          const allNullable = r.rhsTokens.every(tok => nullableSet.has(tok));
          if (allNullable) {
            nullableSet.add(r.lhs);
            changed = true;
            currentPassDiscoveries.push({
              variable: r.lhs,
              rule: `${r.lhs} -> ${r.rhsTokens.join(' ')}`,
              tokens: [...r.rhsTokens],
              reason: `Every symbol on RHS [${r.rhsTokens.join(', ')}] is already known to be nullable.`
            });
          }
        }
      }

      phase2Passes.push({
        passNumber,
        discoveries: currentPassDiscoveries,
        snapshot: new Set(nullableSet)
      });

      passNumber++;
      if (passNumber > 50) break; // Infinite loop safety guard
    }

    return {
      nullableSet,
      phase1Logs,
      phase2Passes
    };
  }
}

// 4. COMBINATORIAL REWRITER (Powerset expansion & pruning)
class CombinatorialRewriter {
  static rewrite(rules, nullableSet) {
    const breakdown = [];
    const newProductionsByLhs = {};

    for (let r of rules) {
      if (!newProductionsByLhs[r.lhs]) {
        newProductionsByLhs[r.lhs] = new Set();
      }

      // Case A: Direct Epsilon Rule (Discarded)
      if (r.isEpsilon) {
        breakdown.push({
          type: 'epsilon',
          lhs: r.lhs,
          origRule: `${r.lhs} -> ε`,
          status: 'discarded',
          reason: 'Direct ε-production is discarded to eliminate empty transitions.'
        });
        continue;
      }

      // Case B: Non-Epsilon Rule
      const tokens = r.rhsTokens;
      const nullableIndices = [];
      for (let i = 0; i < tokens.length; i++) {
        if (nullableSet.has(tokens[i])) {
          nullableIndices.push(i);
        }
      }

      const m = nullableIndices.length;

      // Subcase B1: No nullable variables on RHS
      if (m === 0) {
        const resultString = tokens.join(' ');
        newProductionsByLhs[r.lhs].add(resultString);
        breakdown.push({
          type: 'no-nullable',
          lhs: r.lhs,
          origRule: `${r.lhs} -> ${tokens.join(' ')}`,
          tokens,
          status: 'retained',
          reason: 'No nullable variables on RHS; rule is carried over unchanged.',
          resultingAlts: [resultString]
        });
        continue;
      }

      // Subcase B2: m >= 1 nullable variables -> 2^m combinations
      const totalCombinations = 1 << m;
      const comboRows = [];
      const seenAltsInRule = new Set();

      for (let mask = 0; mask < totalCombinations; mask++) {
        let keptTokens = [];
        let tokenStates = [];

        let nullIndexCursor = 0;
        for (let i = 0; i < tokens.length; i++) {
          if (nullableSet.has(tokens[i])) {
            const isKept = (mask & (1 << nullIndexCursor)) !== 0;
            nullIndexCursor++;
            if (isKept) {
              keptTokens.push(tokens[i]);
              tokenStates.push({ text: tokens[i], kept: true, isNullable: true });
            } else {
              tokenStates.push({ text: tokens[i], kept: false, isNullable: true });
            }
          } else {
            keptTokens.push(tokens[i]);
            tokenStates.push({ text: tokens[i], kept: true, isNullable: false });
          }
        }

        const resultStr = keptTokens.join(' ');

        // Check if completely empty
        if (keptTokens.length === 0) {
          comboRows.push({
            tokenStates,
            resultStr: 'ε',
            status: 'discarded',
            statusLabel: 'Discarded (ε)'
          });
        } else if (seenAltsInRule.has(resultStr)) {
          comboRows.push({
            tokenStates,
            resultStr,
            status: 'duplicate',
            statusLabel: 'Duplicate'
          });
        } else {
          seenAltsInRule.add(resultStr);
          newProductionsByLhs[r.lhs].add(resultStr);
          comboRows.push({
            tokenStates,
            resultStr,
            status: 'retained',
            statusLabel: 'Retained'
          });
        }
      }

      breakdown.push({
        type: 'combinatorial',
        lhs: r.lhs,
        origRule: `${r.lhs} -> ${tokens.join(' ')}`,
        tokens,
        nullableIndices,
        comboRows,
        resultingAlts: Array.from(seenAltsInRule)
      });
    }

    return {
      breakdown,
      newProductionsByLhs
    };
  }
}

// 5. GRAMMAR FORMATTER & REPORT GENERATOR
class GrammarFormatter {
  static formatCleanGrammar(allVariables, productionsByLhs) {
    const lines = [];
    for (let v of allVariables) {
      if (productionsByLhs[v] && productionsByLhs[v].size > 0) {
        const alts = Array.from(productionsByLhs[v]);
        lines.push(`${v} -> ${alts.join(' | ')}`);
      }
    }
    return lines.join('\n');
  }

  static generateMarkdownReport(parsed, nullableResult, rewriteResult) {
    const { variables, terminals, startSymbol } = parsed;
    const isStartNullable = nullableResult.nullableSet.has(startSymbol);
    const cleanGrammar = this.formatCleanGrammar(variables, rewriteResult.newProductionsByLhs);

    let md = `# Epsilon-Production Removal Analysis Report\n\n`;
    md += `## 1. Formal Grammar Definition\n`;
    md += `- **Variables (V)**: { ${variables.join(', ')} }\n`;
    md += `- **Terminals (Σ)**: { ${terminals.join(', ')} }\n`;
    md += `- **Start Symbol (S)**: ${startSymbol}\n\n`;

    md += `## 2. Nullable Variables Discovery\n`;
    md += `### Phase 1: Direct Rules\n`;
    if (nullableResult.phase1Logs.length === 0) {
      md += `None.\n`;
    } else {
      nullableResult.phase1Logs.forEach(log => {
        md += `- **${log.variable}**: ${log.reason}\n`;
      });
    }

    md += `\n### Phase 2: Iterative Passes\n`;
    nullableResult.phase2Passes.forEach(pass => {
      md += `**Pass ${pass.passNumber}**:\n`;
      if (pass.discoveries.length === 0) {
        md += `- No new variables discovered (Fixed-point reached).\n`;
      } else {
        pass.discoveries.forEach(d => {
          md += `- Discovered **${d.variable}** via \`${d.rule}\`: ${d.reason}\n`;
        });
      }
    });

    md += `\n**Final Nullable Set**: { ${Array.from(nullableResult.nullableSet).join(', ') || '∅'} }\n\n`;

    md += `## 3. Production Rewriting\n`;
    rewriteResult.breakdown.forEach((b, i) => {
      md += `### Rule ${i + 1}: \`${b.origRule}\`\n`;
      if (b.type === 'epsilon') {
        md += `*Discarded directly (ε-production)*\n\n`;
      } else if (b.type === 'no-nullable') {
        md += `*Unchanged (no nullable variables)* -> \`${b.resultingAlts[0]}\`\n\n`;
      } else {
        md += `Expanded into ${b.resultingAlts.length} unique alternative(s):\n`;
        b.resultingAlts.forEach(alt => {
          md += `- \`${b.lhs} -> ${alt}\`\n`;
        });
        md += `\n`;
      }
    });

    md += `## 4. Final Grammar\n`;
    md += `\`\`\`text\n${cleanGrammar}\n\`\`\`\n\n`;

    if (isStartNullable) {
      let newStart = "S0";
      if (variables.includes("S0")) newStart = "S'";
      md += `### Start Symbol Exception Note\n`;
      md += `The start symbol **${startSymbol}** is nullable, meaning ε ∈ L(G).\n`;
      md += `To preserve the full language, introduce augmented start symbol **${newStart}**:\n\n`;
      md += `\`\`\`text\n${newStart} -> ${startSymbol} | eps\n${cleanGrammar}\n\`\`\`\n`;
    }

    return md;
  }
}

// 6. UI CONTROLLER
class UIController {
  constructor() {
    this.currentAnalysis = null;
    this.initElements();
    this.bindEvents();
  }

  initElements() {
    this.inputCard = document.getElementById('inputCard');
    this.grammarInput = document.getElementById('grammarInput');
    this.btnAnalyze = document.getElementById('btnAnalyze');
    this.btnClear = document.getElementById('btnClear');
    this.errorBanner = document.getElementById('globalErrorBanner');
    this.resultsSection = document.getElementById('resultsSection');

    // Metrics elements
    this.metricVariables = document.getElementById('metricVariables');
    this.metricTerminals = document.getElementById('metricTerminals');
    this.metricOriginalRules = document.getElementById('metricOriginalRules');
    this.metricNullableCount = document.getElementById('metricNullableCount');

    // Step 1 elements
    this.step1Variables = document.getElementById('step1Variables');
    this.step1Terminals = document.getElementById('step1Terminals');
    this.step1StartSymbol = document.getElementById('step1StartSymbol');
    this.step1Rules = document.getElementById('step1Rules');

    // Step 2 elements
    this.step2Phase1 = document.getElementById('step2Phase1');
    this.step2Phase2 = document.getElementById('step2Phase2');
    this.step2Summary = document.getElementById('step2Summary');

    // Step 3 elements
    this.step3Container = document.getElementById('step3Container');
    this.ruleFilterSelect = document.getElementById('ruleFilterSelect');

    // Step 4 elements
    this.step4Alert = document.getElementById('step4Alert');
    this.finalStrictText = document.getElementById('finalStrictText');
    this.finalAugmentedPanel = document.getElementById('finalAugmentedPanel');
    this.finalAugmentedText = document.getElementById('finalAugmentedText');
    this.finalGridContainer = document.getElementById('finalGridContainer');
  }

  bindEvents() {
    this.btnAnalyze.addEventListener('click', () => this.analyze());
    this.btnClear.addEventListener('click', () => this.clear());

    if (this.ruleFilterSelect) {
      this.ruleFilterSelect.addEventListener('change', (e) => this.filterStep3Rules(e.target.value));
    }

    // ScrollSpy to highlight active tab while scrolling down
    window.addEventListener('scroll', () => this.onScrollSpy());
  }

  scrollToStep(stepId) {
    const el = document.getElementById(stepId);
    if (el) {
      const yOffset = -140; // offset for sticky navbar + sticky stepper
      const y = el.getBoundingClientRect().top + window.pageYOffset + yOffset;
      window.scrollTo({ top: y, behavior: 'smooth' });
    }
  }

  scrollToTop() {
    window.scrollTo({ top: 0, behavior: 'smooth' });
    this.grammarInput.focus();
  }

  onScrollSpy() {
    if (!this.resultsSection || this.resultsSection.style.display === 'none') return;
    const scrollPos = window.pageYOffset + 220;
    const steps = ['step1', 'step2', 'step3', 'step4'];
    let currentActive = 'step1';

    for (let id of steps) {
      const el = document.getElementById(id);
      if (el && el.offsetTop <= scrollPos) {
        currentActive = id;
      }
    }

    document.querySelectorAll('.step-tab').forEach(tab => {
      if (tab.getAttribute('data-target') === currentActive) {
        tab.classList.add('active');
      } else {
        tab.classList.remove('active');
      }
    });
  }

  insertSymbol(sym) {
    const start = this.grammarInput.selectionStart;
    const end = this.grammarInput.selectionEnd;
    const text = this.grammarInput.value;
    this.grammarInput.value = text.substring(0, start) + sym + text.substring(end);
    this.grammarInput.selectionStart = this.grammarInput.selectionEnd = start + sym.length;
    this.grammarInput.focus();
  }

  clear() {
    this.grammarInput.value = '';
    this.resultsSection.style.display = 'none';
    this.currentAnalysis = null;
    this.hideError();
  }

  showError(msg) {
    this.errorBanner.innerHTML = `<strong>Grammar Syntax Notice:</strong> ${this.escape(msg)}`;
    this.errorBanner.style.display = 'flex';
    this.resultsSection.style.display = 'none';
  }

  hideError() {
    this.errorBanner.style.display = 'none';
    this.errorBanner.innerHTML = '';
  }

  escape(str) {
    if (!str) return '';
    return String(str)
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#039;');
  }

  analyze() {
    this.hideError();
    const text = this.grammarInput.value;

    if (!text.trim()) {
      this.showError("Please enter your CFG production rules in the editor above (e.g. S -> A B | c).");
      return;
    }

    let parsed;
    try {
      parsed = CFGParser.parse(text);
    } catch (err) {
      this.showError(err.message);
      return;
    }

    const nullableResult = NullableEngine.compute(parsed.variables, parsed.rules);
    const rewriteResult = CombinatorialRewriter.rewrite(parsed.rules, nullableResult.nullableSet);

    this.currentAnalysis = { parsed, nullableResult, rewriteResult };

    // Update Live Metrics
    this.updateMetrics(parsed, nullableResult, rewriteResult);

    // Render All Steps (all visible in full continuous sequence)
    this.renderStep1(parsed);
    this.renderStep2(nullableResult);
    this.renderStep3(parsed.variables, rewriteResult);
    this.renderStep4(parsed, nullableResult, rewriteResult);

    this.resultsSection.style.display = 'block';

    // Smoothly scroll down to Step 1
    setTimeout(() => {
      this.scrollToStep('step1');
    }, 100);
  }

  updateMetrics(parsed, nullableResult, rewriteResult) {
    let totalOutputAlts = 0;
    for (let v of parsed.variables) {
      if (rewriteResult.newProductionsByLhs[v]) {
        totalOutputAlts += rewriteResult.newProductionsByLhs[v].size;
      }
    }

    this.metricVariables.textContent = parsed.variables.length;
    this.metricTerminals.textContent = parsed.terminals.length;
    this.metricOriginalRules.textContent = parsed.rules.length;
    this.metricNullableCount.textContent = nullableResult.nullableSet.size;
  }

  renderStep1(parsed) {
    this.step1Variables.innerHTML = parsed.variables.map(v => `<span class="tag variable">${this.escape(v)}</span>`).join(' ');
    this.step1Terminals.innerHTML = parsed.terminals.length > 0 
      ? parsed.terminals.map(t => `<span class="tag terminal">${this.escape(t)}</span>`).join(' ')
      : '<span style="color:var(--text-dim); font-style:italic;">None detected</span>';
    this.step1StartSymbol.innerHTML = `<span class="tag variable" style="font-weight:700;">${this.escape(parsed.startSymbol)}</span>`;

    const grouped = {};
    for (let v of parsed.variables) grouped[v] = [];
    for (let r of parsed.rules) {
      grouped[r.lhs].push(r.isEpsilon ? 'ε' : r.rhsTokens.join(' '));
    }

    const ruleLines = [];
    for (let v of parsed.variables) {
      if (grouped[v] && grouped[v].length > 0) {
        ruleLines.push(`${v}  &rarr;  ${grouped[v].join('  |  ')}`);
      }
    }
    this.step1Rules.innerHTML = ruleLines.join('\n');
  }

  renderStep2(nullableResult) {
    // Phase 1
    if (nullableResult.phase1Logs.length === 0) {
      this.step2Phase1.innerHTML = '<div style="font-size:0.88rem; color:var(--text-dim); font-style:italic;">No direct ε-productions found.</div>';
    } else {
      this.step2Phase1.innerHTML = nullableResult.phase1Logs.map(log => `
        <div class="log-item">
          <span class="tag nullable">${this.escape(log.variable)}</span>
          <span style="margin-left:0.5rem;">${this.escape(log.reason)}</span>
        </div>
      `).join('');
    }

    // Phase 2
    let p2Html = '';
    for (let pass of nullableResult.phase2Passes) {
      p2Html += `
        <div class="pass-container">
          <div class="pass-header">
            <span>Pass ${pass.passNumber}</span>
            <span style="font-size:0.8rem; font-weight:600; color:${pass.discoveries.length > 0 ? 'var(--warning-text)' : 'var(--text-dim)'};">
              ${pass.discoveries.length > 0 ? `${pass.discoveries.length} new variable(s) found` : 'Fixed-point reached &check;'}
            </span>
          </div>
      `;

      if (pass.discoveries.length === 0) {
        p2Html += `<div style="font-size:0.85rem; color:var(--text-dim); font-style:italic;">No new variables added during this pass. Fixed-point achieved.</div>`;
      } else {
        for (let d of pass.discoveries) {
          p2Html += `
            <div class="log-item">
              &bull; Discovered <span class="tag nullable">${this.escape(d.variable)}</span> via <code>${this.escape(d.rule)}</code>: ${this.escape(d.reason)}
            </div>
          `;
        }
      }
      p2Html += `</div>`;
    }
    this.step2Phase2.innerHTML = p2Html;

    // Summary
    if (nullableResult.nullableSet.size === 0) {
      this.step2Summary.innerHTML = `<span style="color:var(--text-muted);">Nullable = &empty; (No nullable variables)</span>`;
    } else {
      const tags = Array.from(nullableResult.nullableSet).map(v => `<span class="tag nullable">${this.escape(v)}</span>`).join(' ');
      this.step2Summary.innerHTML = `<span style="color:var(--text-muted); margin-right:0.5rem;">Nullable = { ${tags} }</span>`;
    }
  }

  renderStep3(allVariables, rewriteResult) {
    // Populate filter dropdown
    if (this.ruleFilterSelect) {
      let options = `<option value="all">Show All Non-Terminals</option>`;
      allVariables.forEach(v => {
        options += `<option value="${this.escape(v)}">Only Variable ${this.escape(v)}</option>`;
      });
      this.ruleFilterSelect.innerHTML = options;
    }

    this.renderStep3Cards(rewriteResult.breakdown);
  }

  filterStep3Rules(selectedVar) {
    if (!this.currentAnalysis) return;
    const allCards = this.currentAnalysis.rewriteResult.breakdown;
    if (selectedVar === 'all') {
      this.renderStep3Cards(allCards);
    } else {
      const filtered = allCards.filter(c => c.lhs === selectedVar);
      this.renderStep3Cards(filtered);
    }
  }

  renderStep3Cards(breakdownItems) {
    let html = '';

    for (let item of breakdownItems) {
      if (item.type === 'epsilon') {
        html += `
          <div class="rule-card">
            <div class="rule-header">
              <span class="rule-title">${this.escape(item.origRule)}</span>
              <span class="badge-discarded">Discarded</span>
            </div>
            <div class="rule-content" style="font-size:0.88rem; color:var(--text-muted);">
              ${this.escape(item.reason)}
            </div>
          </div>
        `;
      } else if (item.type === 'no-nullable') {
        html += `
          <div class="rule-card">
            <div class="rule-header">
              <span class="rule-title">${this.escape(item.origRule)}</span>
              <span class="badge-retained">Retained Unchanged</span>
            </div>
            <div class="rule-content" style="font-size:0.88rem; color:var(--text-muted);">
              ${this.escape(item.reason)} Production added: <code>${this.escape(item.resultingAlts[0])}</code>
            </div>
          </div>
        `;
      } else {
        html += `
          <div class="rule-card">
            <div class="rule-header">
              <span class="rule-title">${this.escape(item.origRule)}</span>
              <span style="font-size:0.82rem; color:var(--cyan-text); font-weight:600;">
                ${item.nullableIndices.length} Nullable &rarr; 2<sup>${item.nullableIndices.length}</sup> = ${1 << item.nullableIndices.length} Combinations
              </span>
            </div>
            <div class="rule-content">
              <div style="font-size:0.85rem; color:var(--text-muted); margin-bottom:0.5rem;">
                Nullable symbols on RHS: ${item.nullableIndices.map(idx => `<span class="tag nullable">${this.escape(item.tokens[idx])} (pos ${idx + 1})</span>`).join(' ')}
              </div>

              <table class="combo-table">
                <thead>
                  <tr>
                    <th style="width: 50px;">#</th>
                    <th>Configuration (Kept / Dropped)</th>
                    <th>Generated RHS</th>
                    <th style="width: 140px;">Status</th>
                  </tr>
                </thead>
                <tbody>
        `;

        item.comboRows.forEach((row, i) => {
          const tokensHtml = row.tokenStates.map(t => {
            if (!t.isNullable) {
              return `<span class="token-terminal">${this.escape(t.text)}</span>`;
            }
            return t.kept
              ? `<span class="token-kept">${this.escape(t.text)}</span>`
              : `<span class="token-dropped">${this.escape(t.text)}</span>`;
          }).join(' ');

          let badgeClass = 'badge-retained';
          if (row.status === 'discarded') badgeClass = 'badge-discarded';
          if (row.status === 'duplicate') badgeClass = 'badge-duplicate';

          html += `
            <tr>
              <td style="color:var(--text-dim); font-family:var(--font-mono);">${i + 1}</td>
              <td>${tokensHtml}</td>
              <td style="font-family:var(--font-mono); font-weight:700;">${this.escape(row.resultStr)}</td>
              <td><span class="${badgeClass}">${row.statusLabel}</span></td>
            </tr>
          `;
        });

        html += `
                </tbody>
              </table>

              <div style="margin-top:0.75rem; font-size:0.85rem; color:var(--text-muted);">
                Unique alternatives added to <code>${this.escape(item.lhs)}</code>:
                ${item.resultingAlts.map(alt => `<span class="tag terminal" style="font-weight:700;">${this.escape(alt)}</span>`).join(' ')}
              </div>
            </div>
          </div>
        `;
      }
    }

    this.step3Container.innerHTML = html;
  }

  renderStep4(parsed, nullableResult, rewriteResult) {
    const { variables, startSymbol } = parsed;
    const isStartNullable = nullableResult.nullableSet.has(startSymbol);

    const cleanGrammar = GrammarFormatter.formatCleanGrammar(variables, rewriteResult.newProductionsByLhs);
    this.finalStrictText.textContent = cleanGrammar;

    if (isStartNullable) {
      let newStart = "S0";
      if (variables.includes("S0")) newStart = "S'";
      if (variables.includes(newStart)) newStart = "S_new";

      const augmentedGrammar = `${newStart} -> ${startSymbol} | eps\n` + cleanGrammar;
      this.finalAugmentedText.textContent = augmentedGrammar;

      this.step4Alert.innerHTML = `
        <div class="alert-box warning">
          <div class="alert-icon">⚠️</div>
          <div>
            <strong>Important Start Symbol Exception: Start Symbol <code>${this.escape(startSymbol)}</code> is Nullable!</strong><br />
            Because ${this.escape(startSymbol)} &rArr;<sup>*</sup> &epsilon;, the empty string is in the original grammar's language (&epsilon; &isin; <em>L</em>(<em>G</em>)).<br />
            A strictly &epsilon;-free grammar cannot generate &epsilon;, so the direct grammar on the left generates <em>L</em>(<em>G</em>) &setminus; {&epsilon;}.<br />
            <strong>Standard Textbook Solution (Hopcroft &amp; Ullman, Sipser):</strong> To preserve &epsilon; in <em>L</em>(<em>G</em>) without allowing internal &epsilon;-transitions, we introduce a new start symbol <code>${newStart}</code> with rule <code>${newStart} &rarr; ${this.escape(startSymbol)} | &epsilon;</code>. Because <code>${newStart}</code> never appears on any RHS, &epsilon; is derived only at the root in a single step.
          </div>
        </div>
      `;

      this.finalAugmentedPanel.style.display = 'block';
      this.finalGridContainer.className = 'final-grid two-columns';
    } else {
      this.step4Alert.innerHTML = `
        <div class="alert-box info">
          <div class="alert-icon">ℹ️</div>
          <div>
            <strong>Start Symbol <code>${this.escape(startSymbol)}</code> is NOT Nullable:</strong><br />
            Since the start symbol cannot derive &epsilon;, the empty string is not part of the language (&epsilon; &notin; <em>L</em>(<em>G</em>)). 
            The resulting grammar is strictly &epsilon;-free and generates the exact same language <em>L</em>(<em>G'</em>) = <em>L</em>(<em>G</em>).
          </div>
        </div>
      `;

      this.finalAugmentedPanel.style.display = 'none';
      this.finalGridContainer.className = 'final-grid';
    }
  }

  copyText(elemId, btn) {
    const text = document.getElementById(elemId).textContent;
    navigator.clipboard.writeText(text).then(() => {
      const prev = btn.textContent;
      btn.textContent = 'Copied!';
      btn.style.color = 'var(--success-text)';
      btn.style.borderColor = 'var(--success)';
      setTimeout(() => {
        btn.textContent = prev;
        btn.style.color = '';
        btn.style.borderColor = '';
      }, 1800);
    }).catch(err => {
      console.error('Clipboard error:', err);
    });
  }

  exportReport() {
    if (!this.currentAnalysis) return;
    const { parsed, nullableResult, rewriteResult } = this.currentAnalysis;
    const reportMd = GrammarFormatter.generateMarkdownReport(parsed, nullableResult, rewriteResult);

    const blob = new Blob([reportMd], { type: 'text/markdown;charset=utf-8;' });
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = `CFG_Epsilon_Elimination_Report_${Date.now()}.md`;
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);
    URL.revokeObjectURL(url);
  }
}

// Global App Instance
let app;
window.addEventListener('DOMContentLoaded', () => {
  app = new UIController();
});
