'use strict';
// =====================================================================
//  latex.js — 論理式の LaTeX 表示と, 証明木の bussproofs 出力
//  表示上の約束:
//    * 二分岐のノードは MP (左が前件 φ, 右が φ→ψ), 一分岐のノードは Gen.
//    * 葉の右肩に公理の種類 (A1–A6, 公理名, 定義公理名, 定理番号) を記す.
//    * 長い論理式は φ_k などで略記し, 木の後に一覧を付ける(略記は記号列の省略にすぎない).
// =====================================================================
const C = require('./core');
const L = require('./lang');
const { desugar, key } = C;

// ---------- 変数名の表示 ----------
const greek = { eps: '\\varepsilon', al: '\\alpha', be: '\\beta', ga: '\\gamma', de: '\\delta', et: '\\eta', th: '\\theta', la: '\\lambda', mu: '\\mu', xi: '\\xi', rho: '\\rho', si: '\\sigma', ta: '\\tau', ph: '\\varphi' };
function texVar(n) {
  if (n.includes('_{')) return n;
  let m = n.match(/^([A-Za-z]+?)(\d+)('*)$/);
  let base = n, sub = '', pr = '';
  if (m) { base = m[1]; sub = m[2]; pr = m[3]; }
  else { m = n.match(/^([A-Za-z]+)('*)$/); if (m) { base = m[1]; pr = m[2]; } }
  let b = greek[base] ?? (base.length > 1 ? `\\mathit{${base}}` : base);
  return b + (sub ? `_{${sub}}` : '') + pr;
}
const seqVars = new Set(['a', 'b', 'c', 's', 'u', 'w']);
// app(g(…), n) の表示 (例: 累乗 r^n, 部分和 Σ). appHook: 関数記号 → (g の引数, n) ↦ 文字列
const appHook = new Map();

// ---------- 項 ----------
function texT(t, outer = 0) {
  if (t.k === 'var') return texVar(t.n);
  const fd = L.funcs.get(t.f);
  if (!fd) throw new Error('未登録の関数記号 ' + t.f);
  if (t.f === 'app' && t.a[0].k === 'app' && appHook.has(t.a[0].f)) return appHook.get(t.a[0].f)(t.a[0].a, t.a[1]);
  if (t.f === 'app' && t.a[0].k === 'var' && seqVars.has(t.a[0].n)) {
    return `${texVar(t.a[0].n)}_{${texT(t.a[1])}}`;
  }
  let args;
  if (['+', '-'].includes(t.f)) args = [texT(t.a[0], 10), texT(t.a[1], 11)];
  else if (t.f === '*') args = [texT(t.a[0], 20), texT(t.a[1], 21)];
  else if (t.f === 'neg') args = [texT(t.a[0], 31)];
  else if (t.f === 'inv') args = [texT(t.a[0], 41)];
  else args = t.a.map(u => texT(u, 0));
  const s = fd.tex(args);
  return fd.prec < outer ? `(${s})` : s;
}

// ---------- 論理式 ----------
const names = new Map();      // キー → 略記名 (LaTeX)
const patterns = [];          // f ↦ string | null (表示用の記法)
function addPattern(fn) { patterns.push(fn); }
function nameFormula(f, tex) { names.set(key(f), tex); }

// 優先順位: 5 原子・量化子・否定, 3 ∧, 2.5 ∨, 2 →, 1 ↔
function texF(f, top = false) {
  const k = key(f);
  if (!top && names.has(k)) return { s: names.get(k), p: 5 };
  for (const pt of patterns) { const r = pt(f); if (r) return { s: r, p: 5 }; }
  const wrap = (r, min) => (r.p >= min ? r.s : `(${r.s})`);
  switch (f.k) {
    case 'eq': return { s: `${texT(f.a)} = ${texT(f.b)}`, p: 5 };
    case 'le': return { s: `${texT(f.a)} \\leq ${texT(f.b)}`, p: 5 };
    case 'rel': {
      const pd = L.preds.get(f.r);
      if (!pd) throw new Error('未登録の関係記号 ' + f.r);
      return { s: pd.tex(f.a.map(t => texT(t))), p: 5 };
    }
    case 'not': {
      const a = f.a;
      if (a.k === 'eq') return { s: `${texT(a.a)} \\neq ${texT(a.b)}`, p: 5 };
      if (a.k === 'rel' && a.r === 'in') return { s: `${texT(a.a[0])} \\notin ${texT(a.a[1])}`, p: 5 };
      return { s: `\\neg ${wrap(texF(a), 5)}`, p: 5 };
    }
    case 'and': return { s: `${wrap(texF(f.a), 3)} \\land ${wrap(texF(f.b), 3.5)}`, p: 3 };
    case 'or': return { s: `${wrap(texF(f.a), 2.5)} \\lor ${wrap(texF(f.b), 3)}`, p: 2.5 };
    case 'imp': return { s: `${wrap(texF(f.a), 2.5)} \\to ${wrap(texF(f.b), 2)}`, p: 2 };
    case 'iff': return { s: `${wrap(texF(f.a), 2)} \\leftrightarrow ${wrap(texF(f.b), 2)}`, p: 1 };
    case 'all': case 'ex': {
      const q = f.k === 'all' ? '\\forall' : '\\exists';
      // 有界量化子 ∀x∈A(φ), ∃x∈A(φ)
      const b = f.a;
      if (f.k === 'all' && b.k === 'imp' && b.a.k === 'rel' && b.a.r === 'in' && b.a.a[0].k === 'var' && b.a.a[0].n === f.v)
        return { s: `${q} ${texVar(f.v)} \\in ${texT(b.a.a[1])}\\,${quantBody(b.b)}`, p: 5 };
      if (f.k === 'ex' && b.k === 'and' && b.a.k === 'rel' && b.a.r === 'in' && b.a.a[0].k === 'var' && b.a.a[0].n === f.v)
        return { s: `${q} ${texVar(f.v)} \\in ${texT(b.a.a[1])}\\,${quantBody(b.b)}`, p: 5 };
      return { s: `${q} ${texVar(f.v)}\\,${quantBody(b)}`, p: 5 };
    }
  }
  throw new Error('texF: ' + f.k);
}
function quantBody(b) {
  const r = texF(b);
  if ((b.k === 'all' || b.k === 'ex') && !names.has(key(b))) return r.s;
  return `(${r.s})`;
}
const tex = (f, top) => texF(f, top).s;

// 表示幅の概算(単位: 文字)
function width(s) {
  return s
    .replace(/\\(mathit|mathrm|mathsf|text)\{([^}]*)\}/g, '$2')
    .replace(/_\{([^}]*)\}/g, (m, a) => 'x'.repeat(Math.ceil(a.length * 0.6)))
    .replace(/\^\{([^}]*)\}/g, (m, a) => 'x'.repeat(Math.ceil(a.length * 0.6)))
    .replace(/\\(,|;|!|quad)/g, ' ')
    .replace(/\\[a-zA-Z]+/g, 'X')
    .replace(/[{}]/g, '')
    .replace(/\s+/g, '').length;
}

// ---------- 証明木の出力 ----------
const leafLabel = new Map(); // 定理名・公理名 → 表示ラベル
function labelOf(n) {
  if (/^A[1-6]$/.test(n.rule)) return n.rule;
  return leafLabel.get(n.rule + ':' + n.name) ?? leafLabel.get(n.name) ?? n.name;
}
const OPT = { maxFormula: 30, maxWidth: 80, maxHeight: 16, gap: 4 };

function emitProof(root, opt = {}) {
  const o = Object.assign({}, OPT, opt);
  // 1. ノード収集と参照数
  const nodes = []; const ref = new Map();
  (function walk(n) {
    ref.set(n, (ref.get(n) ?? 0) + 1);
    if (ref.get(n) > 1) return;
    n.prem.forEach(walk); nodes.push(n);
  })(root);
  // 2. 略記: 長い論理式に名前を付ける(短いものから順に)
  const local = []; let cnt = 0;
  const saved = new Map(names);
  const forms = new Map();
  for (const n of nodes) forms.set(key(n.f), n.f);
  // 部分論理式も候補に入れる(含意の連鎖の各後件)
  for (const f of [...forms.values()]) { let g = f; while (g.k === 'imp') { forms.set(key(g.b), g.b); forms.set(key(g.a), g.a); g = g.b; } }
  const sorted = [...forms.values()].sort((a, b) => C.show(a).length - C.show(b).length);
  for (const f of sorted) {
    const k = key(f);
    if (names.has(k)) continue;
    const s = tex(f, true);
    if (width(s) > o.maxFormula) {
      const nm = `\\varphi_{${++cnt}}`;
      names.set(k, nm); local.push([nm, f]);
    }
  }
  // 3. 分割: 共有ノードと, 幅・高さの超過
  const sub = new Map(); let pc = 0; // node → Π 番号
  const fw = n => width(tex(n.f)) + (n.prem.length === 0 ? 4 : 0);
  function measure(n, isRoot) {
    if (!isRoot && sub.has(n)) return { w: fw(n) + 3, h: 2 };
    if (n.prem.length === 0) return { w: fw(n), h: 1 };
    let ms = n.prem.map(c => measure(c, false));
    for (;;) {
      const w = Math.max(fw(n), ms.reduce((a, m) => a + m.w, 0) + o.gap * (ms.length - 1));
      const h = 1 + Math.max(...ms.map(m => m.h));
      if (w <= o.maxWidth && h <= o.maxHeight) return { w, h };
      // 最も大きい子を切り出す
      let bi = -1, bv = -1;
      n.prem.forEach((c, i) => { if (!sub.has(c) && c.prem.length > 0) { const v = ms[i].w * 2 + ms[i].h; if (v > bv) { bv = v; bi = i; } } });
      if (bi < 0) return { w, h };
      sub.set(n.prem[bi], 0);
      ms = n.prem.map(c => measure(c, false));
    }
  }
  const sizeMemo = new Map();
  const size = n => { if (sizeMemo.has(n)) return sizeMemo.get(n); const s = 1 + n.prem.reduce((a, c) => a + size(c), 0); sizeMemo.set(n, s); return s; };
  for (const n of nodes) if (ref.get(n) > 1 && n.prem.length > 0 && n !== root && size(n) > 6) sub.set(n, 0);
  measure(root, true);
  // 部分木の中も測る(再帰的に)
  let changed = true;
  while (changed) { changed = false; for (const n of [...sub.keys()]) { const before = sub.size; measure(n, true); if (sub.size !== before) changed = true; } }
  // 番号付け(依存順: 葉に近いものから)
  const order = nodes.filter(n => sub.has(n));
  order.forEach(n => sub.set(n, ++pc));
  // 4. bussproofs 出力
  function emit(n, isRoot) {
    if (!isRoot && sub.has(n)) return `\\AXC{$\\stackrel{\\Pi_{${sub.get(n)}}}{\\vdots}$}\\noLine\n\\UIC{$${tex(n.f)}$}\n`;
    if (n.prem.length === 0) return `\\AXC{$${tex(n.f)}$\\lbl{${labelOf(n)}}}\n`;
    if (n.rule === 'Gen') return emit(n.prem[0], false) + `\\UIC{$${tex(n.f)}$}\n`;
    return emit(n.prem[0], false) + emit(n.prem[1], false) + `\\BIC{$${tex(n.f)}$}\n`;
  }
  let out = '';
  for (const n of order) out += `\\noindent$\\Pi_{${sub.get(n)}}$:\n\\begin{ptree}\n${emit(n, true)}\\end{ptree}\n`;
  out += `\\noindent 主木:\n\\begin{ptree}\n${emit(root, true)}\\end{ptree}\n`;
  if (local.length) {
    out += '\\begin{abbrevlist}\n';
    for (const [nm, f] of local) { const k = key(f); names.delete(k); out += `\\item $${nm} :\\equiv ${tex(f, true)}$\n`; names.set(k, nm); }
    out += '\\end{abbrevlist}\n';
  }
  // 局所略記を消す
  for (const [nm, f] of local) names.delete(key(f));
  for (const [k, v] of saved) names.set(k, v);
  const stats = { nodes: nodes.length, leaves: nodes.filter(n => n.prem.length === 0).length, subs: pc };
  return { tex: out, stats };
}

module.exports = { appHook, texT, texF, tex, texVar, names, nameFormula, addPattern, emitProof, leafLabel, seqVars, width, OPT };
