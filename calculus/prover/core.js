'use strict';
// =====================================================================
//  core.js — 一階述語論理の構文・代入・トートロジー判定・公理検査
//  体系 H: Enderton §2.4 の公理群 1–6 + 推論規則 MP, Gen (Monk Def.10.23 型)
//  原始記号: ¬, →, ∀, =  (∧, ∨, ↔, ∃, ≤ は略記)
// =====================================================================

// ---------- 構成子 ----------
const V = n => ({ k: 'var', n });
const F = (f, ...a) => ({ k: 'app', f, a });
const Eq = (a, b) => ({ k: 'eq', a, b });
const Rel = (r, ...a) => ({ k: 'rel', r, a });
const Not = a => ({ k: 'not', a });
const Imp = (a, b) => ({ k: 'imp', a, b });
const All = (v, a) => ({ k: 'all', v, a });
// 略記(表示用に保持し, 判定時は展開する)
const And = (a, b) => ({ k: 'and', a, b });
const Or = (a, b) => ({ k: 'or', a, b });
const Iff = (a, b) => ({ k: 'iff', a, b });
const Ex = (v, a) => ({ k: 'ex', v, a });
const Le = (a, b) => ({ k: 'le', a, b });       // a ≤ b :≡ a < b ∨ a = b

const isFormula = f => f && ['eq', 'rel', 'not', 'imp', 'all', 'and', 'or', 'iff', 'ex', 'le'].includes(f.k);

// ---------- 項の文字列キー ----------
function tkey(t) {
  if (t.k === 'var') return t.n;
  return t.f + '(' + t.a.map(tkey).join(',') + ')';
}

// ---------- 略記の展開 (Enderton の略記) ----------
const dsMemo = new WeakMap();
function desugar(f) {
  if (dsMemo.has(f)) return dsMemo.get(f);
  let r;
  switch (f.k) {
    case 'eq': case 'rel': r = f; break;
    case 'not': r = Not(desugar(f.a)); break;
    case 'imp': r = Imp(desugar(f.a), desugar(f.b)); break;
    case 'all': r = All(f.v, desugar(f.a)); break;
    case 'and': r = Not(Imp(desugar(f.a), Not(desugar(f.b)))); break;          // α∧β :≡ ¬(α→¬β)
    case 'or': r = Imp(Not(desugar(f.a)), desugar(f.b)); break;                // α∨β :≡ ¬α→β
    case 'iff': { const a = desugar(f.a), b = desugar(f.b); r = Not(Imp(Imp(a, b), Not(Imp(b, a)))); break; }
    case 'ex': r = Not(All(f.v, Not(desugar(f.a)))); break;                    // ∃xα :≡ ¬∀x¬α
    case 'le': r = Imp(Not(Rel('<', f.a, f.b)), Eq(f.a, f.b)); break;         // a≤b :≡ a<b ∨ a=b
    default: throw new Error('desugar: unknown ' + f.k);
  }
  dsMemo.set(f, r);
  return r;
}

// 原始記号のみの論理式のキー
const keyMemo = new WeakMap();
function pkey(f) { // f は desugar 済み
  if (keyMemo.has(f)) return keyMemo.get(f);
  let s;
  switch (f.k) {
    case 'eq': s = '=(' + tkey(f.a) + ',' + tkey(f.b) + ')'; break;
    case 'rel': s = f.r + '(' + f.a.map(tkey).join(',') + ')'; break;
    case 'not': s = '~' + pkey(f.a); break;
    case 'imp': s = '(' + pkey(f.a) + '>' + pkey(f.b) + ')'; break;
    case 'all': s = 'A' + f.v + '.' + pkey(f.a); break;
  }
  keyMemo.set(f, s);
  return s;
}
const key = f => pkey(desugar(f));
const same = (f, g) => key(f) === key(g);

// ---------- 自由変数 ----------
function fvT(t, s = new Set()) {
  if (t.k === 'var') s.add(t.n); else t.a.forEach(u => fvT(u, s));
  return s;
}
function fv(f, s = new Set()) {
  switch (f.k) {
    case 'eq': case 'le': fvT(f.a, s); fvT(f.b, s); break;
    case 'rel': f.a.forEach(t => fvT(t, s)); break;
    case 'not': fv(f.a, s); break;
    case 'imp': case 'and': case 'or': case 'iff': fv(f.a, s); fv(f.b, s); break;
    case 'all': case 'ex': { const t = fv(f.a, new Set()); t.delete(f.v); t.forEach(x => s.add(x)); break; }
  }
  return s;
}
function allVars(f, s = new Set()) { // 現れるすべての変数(束縛も含む)
  const tv = t => { if (t.k === 'var') s.add(t.n); else t.a.forEach(tv); };
  switch (f.k) {
    case 'eq': case 'le': tv(f.a); tv(f.b); break;
    case 'rel': f.a.forEach(tv); break;
    case 'not': allVars(f.a, s); break;
    case 'imp': case 'and': case 'or': case 'iff': allVars(f.a, s); allVars(f.b, s); break;
    case 'all': case 'ex': s.add(f.v); allVars(f.a, s); break;
  }
  return s;
}

// ---------- 代入 (Enderton の定義. 束縛変数の付け替えはしない) ----------
function substT(u, x, t) {
  if (u.k === 'var') return u.n === x ? t : u;
  return F(u.f, ...u.a.map(v => substT(v, x, t)));
}
function subst(f, x, t) {
  switch (f.k) {
    case 'eq': return Eq(substT(f.a, x, t), substT(f.b, x, t));
    case 'le': return Le(substT(f.a, x, t), substT(f.b, x, t));
    case 'rel': return Rel(f.r, ...f.a.map(u => substT(u, x, t)));
    case 'not': return Not(subst(f.a, x, t));
    case 'imp': return Imp(subst(f.a, x, t), subst(f.b, x, t));
    case 'and': return And(subst(f.a, x, t), subst(f.b, x, t));
    case 'or': return Or(subst(f.a, x, t), subst(f.b, x, t));
    case 'iff': return Iff(subst(f.a, x, t), subst(f.b, x, t));
    case 'all': return f.v === x ? f : All(f.v, subst(f.a, x, t));
    case 'ex': return f.v === x ? f : Ex(f.v, subst(f.a, x, t));
  }
}
// t が f の x に代入可能か (Enderton §2.4)
function substitutable(t, x, f) {
  switch (f.k) {
    case 'eq': case 'rel': case 'le': return true;
    case 'not': return substitutable(t, x, f.a);
    case 'imp': case 'and': case 'or': case 'iff': return substitutable(t, x, f.a) && substitutable(t, x, f.b);
    case 'all': case 'ex':
      if (!fv(f).has(x)) return true;
      return !fvT(t).has(f.v) && substitutable(t, x, f.a);
  }
}
// 同時代入(相異なる変数. 新しい変数を経由して逐次代入と同等にする)
function substMany(f, xs, ts) {
  return xs.reduce((g, x, i) => subst(g, x, ts[i]), f);
}

// ---------- トートロジー判定 (Tseitin 変換 + DPLL) ----------
function isTautology(f) {
  const g = desugar(f);
  const primeId = new Map(); let nv = 0; const clauses = [];
  const memo = new Map();
  function enc(h) { // h の真偽を表すリテラルを返す
    const k = pkey(h);
    if (memo.has(k)) return memo.get(k);
    let lit;
    if (h.k === 'not') lit = -enc(h.a);
    else if (h.k === 'imp') {
      const a = enc(h.a), b = enc(h.b); const v = ++nv; lit = v;
      // v ↔ (¬a ∨ b)
      clauses.push([-v, -a, b]); clauses.push([v, a]); clauses.push([v, -b]);
    } else { // 素論理式
      if (!primeId.has(k)) primeId.set(k, ++nv);
      lit = primeId.get(k);
    }
    memo.set(k, lit);
    return lit;
  }
  const top = enc(g);
  clauses.push([-top]);
  return !sat(clauses, nv);
}
function sat(clauses, nv) {
  const assign = new Int8Array(nv + 1);
  function val(l) { const a = assign[Math.abs(l)]; return a === 0 ? 0 : (l > 0 ? a : -a); }
  function dpll(trail) {
    // 単位伝播
    let changed = true;
    while (changed) {
      changed = false;
      for (const c of clauses) {
        let unassigned = 0, last = 0, satisfied = false;
        for (const l of c) { const v = val(l); if (v === 1) { satisfied = true; break; } if (v === 0) { unassigned++; last = l; } }
        if (satisfied) continue;
        if (unassigned === 0) return false;
        if (unassigned === 1) { assign[Math.abs(last)] = last > 0 ? 1 : -1; trail.push(Math.abs(last)); changed = true; }
      }
    }
    let pick = 0;
    for (let i = 1; i <= nv; i++) if (assign[i] === 0) { pick = i; break; }
    if (!pick) return true;
    for (const b of [1, -1]) {
      const t2 = [];
      assign[pick] = b; t2.push(pick);
      if (dpll(t2)) return true;
      for (const v of t2) assign[v] = 0;
    }
    return false;
  }
  return dpll([]);
}

// ---------- 公理群の判定 ----------
// A2: ∀xα → α^x_t (t は代入可能)
function matchInst(alpha, beta, x) { // α^x_t ≡ β となる t を探す. 見つからなければ undefined
  let found = null; let ok = true;
  function mt(a, b) {
    if (!ok) return;
    if (a.k === 'var' && a.n === x) {
      if (found === null) found = b; else if (tkey(found) !== tkey(b)) ok = false;
      return;
    }
    if (a.k === 'var') { if (!(b.k === 'var' && b.n === a.n)) ok = false; return; }
    if (b.k !== 'app' || b.f !== a.f || b.a.length !== a.a.length) { ok = false; return; }
    a.a.forEach((u, i) => mt(u, b.a[i]));
  }
  function mf(a, b) {
    if (!ok) return;
    if (a.k !== b.k) { ok = false; return; }
    switch (a.k) {
      case 'eq': mt(a.a, b.a); mt(a.b, b.b); break;
      case 'rel': if (a.r !== b.r || a.a.length !== b.a.length) { ok = false; return; } a.a.forEach((u, i) => mt(u, b.a[i])); break;
      case 'not': mf(a.a, b.a); break;
      case 'imp': mf(a.a, b.a); mf(a.b, b.b); break;
      case 'all':
        if (a.v !== b.v) { ok = false; return; }
        if (a.v === x) { if (pkey(a) !== pkey(b)) ok = false; return; }
        mf(a.a, b.a); break;
    }
  }
  mf(alpha, beta);
  if (!ok) return undefined;
  return found === null ? V(x) : found;
}
function checkA2(f) {
  const g = desugar(f);
  if (g.k !== 'imp' || g.a.k !== 'all') return 'A2: 形が ∀xα→β でない';
  const x = g.a.v, alpha = g.a.a, beta = g.b;
  const t = matchInst(alpha, beta, x);
  if (t === undefined) return 'A2: β は α^x_t の形でない';
  if (!substitutable(t, x, alpha)) return 'A2: 項が代入可能でない';
  return null;
}
function checkA3(f) {
  const g = desugar(f);
  // ∀x(α→β) → (∀xα → ∀xβ)
  if (g.k === 'imp' && g.a.k === 'all' && g.a.a.k === 'imp' && g.b.k === 'imp' && g.b.a.k === 'all' && g.b.b.k === 'all') {
    const x = g.a.v;
    if (g.b.a.v === x && g.b.b.v === x && pkey(g.a.a.a) === pkey(g.b.a.a) && pkey(g.a.a.b) === pkey(g.b.b.a)) return null;
  }
  return 'A3: 形が合わない';
}
function checkA4(f) {
  const g = desugar(f);
  if (g.k === 'imp' && g.b.k === 'all' && pkey(g.a) === pkey(g.b.a) && !fv(g.a).has(g.b.v)) return null;
  return 'A4: 形が α→∀xα (x は α に自由に現れない) でない';
}
function checkA5(f) {
  const g = desugar(f);
  if (g.k === 'eq' && g.a.k === 'var' && g.b.k === 'var' && g.a.n === g.b.n) return null;
  return 'A5: x = x の形でない';
}
function checkA6(f) {
  const g = desugar(f);
  if (!(g.k === 'imp' && g.a.k === 'eq' && g.a.a.k === 'var' && g.a.b.k === 'var' && g.b.k === 'imp')) return 'A6: 形が x=y→(α→α\') でない';
  const x = g.a.a.n, y = g.a.b.n, a = g.b.a, b = g.b.b;
  if (!['eq', 'rel'].includes(a.k) || a.k !== b.k) return 'A6: α が原子論理式でない';
  let ok = true;
  function ct(s, t) {
    if (!ok) return;
    if (s.k === 'var') { if (t.k === 'var' && (t.n === s.n || (s.n === x && t.n === y))) return; ok = false; return; }
    if (t.k !== 'app' || t.f !== s.f || t.a.length !== s.a.length) { ok = false; return; }
    s.a.forEach((u, i) => ct(u, t.a[i]));
  }
  if (a.k === 'eq') { ct(a.a, b.a); ct(a.b, b.b); }
  else { if (a.r !== b.r || a.a.length !== b.a.length) return 'A6: 関係記号が違う'; a.a.forEach((u, i) => ct(u, b.a[i])); }
  return ok ? null : "A6: α' は α の x の一部を y に置き換えたものでない";
}

// ---------- 証明ノードと理論 ----------
// node = { rule, f, prem:[...], name? }
//   rule ∈ 'A1'..'A6', 'Ax'(理論の公理), 'Def'(定義公理), 'Thm'(既証定理), 'MP', 'Gen'
const Theory = {
  axioms: new Map(),      // 名前 → 論理式 (ZFC の公理など)
  schemas: new Map(),     // 図式名 → 判定関数 f ↦ bool
  defs: new Map(),        // 名前 → 定義公理
  thms: new Map(),        // 名前 → { f, node | null, status }
};
let nodeCount = 0;
function mkLeaf(rule, f, name) {
  let err = null;
  switch (rule) {
    case 'A1': if (!isTautology(f)) err = 'A1: トートロジーでない'; break;
    case 'A2': err = checkA2(f); break;
    case 'A3': err = checkA3(f); break;
    case 'A4': err = checkA4(f); break;
    case 'A5': err = checkA5(f); break;
    case 'A6': err = checkA6(f); break;
    case 'Ax': {
      if (Theory.axioms.has(name)) { if (!same(Theory.axioms.get(name), f)) err = 'Ax ' + name + ': 論理式が公理と一致しない'; }
      else if (Theory.schemas.has(name)) { if (!Theory.schemas.get(name)(f)) err = 'Ax ' + name + ': 図式のインスタンスでない'; }
      else err = '未登録の公理 ' + name;
      break;
    }
    case 'Def': if (!Theory.defs.has(name) || !same(Theory.defs.get(name), f)) err = 'Def ' + name + ': 定義公理と一致しない'; break;
    case 'Thm': if (!Theory.thms.has(name) || !same(Theory.thms.get(name).f, f)) err = 'Thm ' + name + ': 定理と一致しない'; break;
    default: err = 'unknown rule ' + rule;
  }
  if (err) throw new Error(err + '\n  論理式: ' + show(f));
  nodeCount++;
  return { rule, f, prem: [], name };
}
function mkMP(minor, major) {
  const g = desugar(major.f);
  if (g.k !== 'imp' || pkey(g.a) !== key(minor.f)) throw new Error('MP: 前件が一致しない\n  minor: ' + show(minor.f) + '\n  major: ' + show(major.f));
  // 結論は major の後件(略記を保つため major.f の構造から取り出す)
  const c = consequent(major.f);
  nodeCount++;
  return { rule: 'MP', f: c, prem: [minor, major] };
}
function consequent(f) {
  if (f.k === 'imp') return f.b;
  if (f.k === 'or') return f.b; // ¬a→b
  return desugar(f).b;
}
function mkGen(p, x) {
  nodeCount++;
  return { rule: 'Gen', f: All(x, p.f), prem: [p], v: x };
}

// ---------- 簡易表示 (エラーメッセージ用) ----------
function showT(t) {
  if (t.k === 'var') return t.n;
  if (t.a.length === 0) return t.f;
  return t.f + '(' + t.a.map(showT).join(',') + ')';
}
function show(f) {
  switch (f.k) {
    case 'eq': return showT(f.a) + '=' + showT(f.b);
    case 'le': return showT(f.a) + '≤' + showT(f.b);
    case 'rel': return f.r + '(' + f.a.map(showT).join(',') + ')';
    case 'not': return '¬' + show(f.a);
    case 'imp': return '(' + show(f.a) + '→' + show(f.b) + ')';
    case 'and': return '(' + show(f.a) + '∧' + show(f.b) + ')';
    case 'or': return '(' + show(f.a) + '∨' + show(f.b) + ')';
    case 'iff': return '(' + show(f.a) + '↔' + show(f.b) + ')';
    case 'all': return '∀' + f.v + ' ' + show(f.a);
    case 'ex': return '∃' + f.v + ' ' + show(f.a);
  }
}

// ---------- 検証 (木全体を再検査する) ----------
function verify(node, seen = new Set()) {
  if (seen.has(node)) return;
  seen.add(node);
  if (node.prem.length === 0) { mkLeaf(node.rule, node.f, node.name); return; }
  node.prem.forEach(p => verify(p, seen));
  if (node.rule === 'MP') {
    const [mi, ma] = node.prem; const g = desugar(ma.f);
    if (!(g.k === 'imp' && pkey(g.a) === key(mi.f) && pkey(g.b) === key(node.f))) throw new Error('verify MP failed: ' + show(node.f));
  } else if (node.rule === 'Gen') {
    if (!(node.f.k === 'all' && node.f.v === node.v && same(node.f.a, node.prem[0].f))) throw new Error('verify Gen failed');
  } else throw new Error('bad internal rule');
}

module.exports = {
  V, F, Eq, Rel, Not, Imp, All, And, Or, Iff, Ex, Le, isFormula,
  tkey, desugar, key, same, fv, fvT, allVars, subst, substT, substitutable, substMany,
  isTautology, Theory, mkLeaf, mkMP, mkGen, verify, show, showT, consequent,
  getNodeCount: () => nodeCount,
};
