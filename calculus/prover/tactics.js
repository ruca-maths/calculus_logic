'use strict';
// =====================================================================
//  tactics.js — 証明を組み立てるための補助関数
//  すべての補助関数は, 公理 (A1)–(A6), 理論の公理・定義公理・既証定理の葉と,
//  推論規則 MP, Gen のノードだけからなる木を作る(導出規則は残らない).
//
//  「行」 Line = 文脈 ctx = [h1,...,hk] と論理式 φ の組で,
//  その証明木の根の論理式は h1 → (h2 → ... (hk → φ)) である.
// =====================================================================
const C = require('./core');
const L = require('./lang');
const { V, F, Eq, Rel, Not, Imp, All, And, Ex, Iff, desugar, key, same, fv, fvT, subst, substT, mkLeaf, mkMP, mkGen, show } = C;

const curry = (ctx, phi) => ctx.reduceRight((acc, h) => Imp(h, acc), phi);
class Line {
  constructor(ctx, phi, node) {
    this.ctx = ctx; this.phi = phi; this.node = node;
    if (!same(node.f, curry(ctx, phi))) throw new Error('Line: 根の論理式が文脈と一致しない\n  ' + show(node.f) + '\n  ' + show(curry(ctx, phi)));
  }
}
const P = (s, env) => (typeof s === 'string' ? L.parse(s, env) : s);
const T = (s, env) => (typeof s === 'string' ? L.parseTerm(s, env) : s);

// ---------- 葉 ----------
function ax(rule, f, name) { const g = P(f); return new Line([], g, mkLeaf(rule, g, name)); }
const axiom = (name, f) => ax('Ax', f ?? C.Theory.axioms.get(name), name);
const defAx = name => ax('Def', C.Theory.defs.get(name), name);
const thm = name => {
  const t = C.Theory.thms.get(name);
  if (!t) throw new Error('未登録の定理 ' + name);
  return ax('Thm', t.f, name);
};

// ---------- MP の連鎖による命題論理的推論 (A1 と MP のみ) ----------
// prems の各行から, 文脈 ctx のもとで goal をトートロジー的に導く.
function tc(ctx, prems, goal) {
  prems = prems.slice();
  goal = P(goal);
  for (const p of prems) if (p.ctx.length === ctx.length && p.ctx.every((h, i) => same(h, ctx[i])) && same(p.phi, goal)) return new Line(ctx, goal, p.node);
  const target = curry(ctx, goal);
  for (const p of prems) if (same(p.node.f, target)) return new Line(ctx, goal, p.node);
  let taut = prems.reduceRight((acc, p) => Imp(p.node.f, acc), target);
  if (!C.isTautology(taut)) {
    // 束縛変数名だけが異なる素論理式 ∀uα, ∀wα[u:=w] の同値を補う
    const extra = alphaLemmas([...prems.map(p => p.node.f), target]);
    if (extra.length) { prems = prems.concat(extra); taut = prems.reduceRight((acc, p) => Imp(p.node.f, acc), target); }
  }
  let leaf;
  try { leaf = mkLeaf('A1', taut); }
  catch (e) {
    throw new Error('tc 失敗: 前提からトートロジー的に従わない\n  goal: ' + show(goal) + '\n  ctx: ' + ctx.map(show).join(' ; ') + '\n  prems:\n    ' + prems.map(p => show(p.node.f)).join('\n    '));
  }
  let n = leaf;
  for (const p of prems) n = mkMP(p.node, n);
  return new Line(ctx, goal, n);
}
// 束縛変数の名前を無視したキー
function akey(f, env = []) {
  switch (f.k) {
    case 'eq': return '=(' + tk(f.a) + ',' + tk(f.b) + ')';
    case 'rel': return f.r + '(' + f.a.map(tk).join(',') + ')';
    case 'not': return '~' + akey(f.a, env);
    case 'imp': return '(' + akey(f.a, env) + '>' + akey(f.b, env) + ')';
    case 'all': return 'A.' + akey(f.a, [f.v, ...env]);
  }
  function tk(t) { if (t.k === 'var') { const i = env.indexOf(t.n); return i >= 0 ? '#' + i : t.n; } return t.f + '(' + t.a.map(tk).join(',') + ')'; }
}
function primesOf(f, out) {
  switch (f.k) {
    case 'not': primesOf(f.a, out); break;
    case 'imp': primesOf(f.a, out); primesOf(f.b, out); break;
    case 'all': out.push(f); break;
  }
  return out;
}
// ⊢ ∀uα → ∀wβ  (β ≡ α[u:=w], w は ∀uα に自由に現れない)
function alphaImp(f, g) {
  const a2 = mkLeaf('A2', Imp(f, g.a));
  const gn = mkGen(a2, g.v);
  const a3 = mkLeaf('A3', Imp(gn.f, Imp(All(g.v, f), g)));
  const a4 = mkLeaf('A4', Imp(f, All(g.v, f)));
  return tc([], [new Line([], gn.f, gn), new Line([], a3.f, a3), new Line([], a4.f, a4)], Imp(f, g));
}
function alphaLemmas(forms) {
  const ps = []; forms.forEach(f => primesOf(desugar(f), ps));
  const groups = new Map();
  for (const p of ps) { const k = akey(p); if (!groups.has(k)) groups.set(k, new Map()); groups.get(k).set(C.key(p), p); }
  const out = [];
  for (const g of groups.values()) {
    const arr = [...g.values()];
    for (let i = 0; i < arr.length; i++) for (let j = 0; j < arr.length; j++) if (i !== j) {
      const f = arr[i], h = arr[j];
      if (f.v === h.v) continue;
      if (fv(f).has(h.v) || !C.substitutable(V(h.v), f.v, f.a)) continue;
      if (C.key(subst(f.a, f.v, V(h.v))) !== C.key(h.a)) continue;
      out.push(alphaImp(f, h));
    }
  }
  return out;
}
// 仮定 ctx[i] (または論理式 h) を取り出す
function hyp(ctx, h) {
  const g = typeof h === 'number' ? ctx[h] : P(h);
  if (!ctx.some(c => same(c, g))) throw new Error('hyp: 文脈にない仮定 ' + show(g));
  return new Line(ctx, g, mkLeaf('A1', curry(ctx, g)));
}
const mp = (ctx, imp, a) => tc(ctx, [imp, a], consequentOf(imp.phi));
function consequentOf(f) { if (f.k === 'imp') return f.b; const g = desugar(f); if (g.k === 'imp') return g.b; throw new Error('mp: 含意でない'); }

// ---------- 汎化 ----------
function conj(ctx) { return ctx.slice(1).reduce((a, h) => And(a, h), ctx[0]); }
function gen(line, x) {
  const { ctx, phi } = line;
  for (const h of ctx) if (fv(h).has(x)) throw new Error('gen: 変数 ' + x + ' が仮定 ' + show(h) + ' に自由に現れる');
  if (ctx.length === 0) return new Line([], All(x, phi), mkGen(line.node, x));
  const H = conj(ctx);
  const l1 = ctx.length === 1 ? line : tc([], [line], Imp(H, phi));
  const g = mkGen(l1.node, x);
  const a3 = mkLeaf('A3', Imp(All(x, Imp(H, phi)), Imp(All(x, H), All(x, phi))));
  const a4 = mkLeaf('A4', Imp(H, All(x, H)));
  const lines = [new Line([], g.f, g), new Line([], a3.f, a3), new Line([], a4.f, a4)];
  return tc(ctx, lines, All(x, phi));
}
const genAll = (line, xs) => xs.slice().reverse().reduce((l, x) => gen(l, x), line);


// ---------- α 変換 (束縛変数の付け替え) ----------
// 束縛変数のうち avoid に属するものを新しい変数に付け替えた論理式(略記の形を保つ)
let alphaN = 0;
function renameBound(f, avoid, used) {
  const nv = () => { let w; do { w = 'u' + (++alphaN); } while (used.has(w) || avoid.has(w)); used.add(w); return w; };
  switch (f.k) {
    case 'eq': case 'rel': case 'le': return f;
    case 'not': return C.Not(renameBound(f.a, avoid, used));
    case 'imp': return C.Imp(renameBound(f.a, avoid, used), renameBound(f.b, avoid, used));
    case 'and': return C.And(renameBound(f.a, avoid, used), renameBound(f.b, avoid, used));
    case 'or': return C.Or(renameBound(f.a, avoid, used), renameBound(f.b, avoid, used));
    case 'iff': return C.Iff(renameBound(f.a, avoid, used), renameBound(f.b, avoid, used));
    case 'all': case 'ex': {
      let v = f.v, body = f.a;
      if (avoid.has(v)) { const w = nv(); body = subst(body, v, V(w)); v = w; }
      body = renameBound(body, avoid, used);
      return f.k === 'all' ? C.All(v, body) : C.Ex(v, body);
    }
  }
  throw new Error('renameBound: ' + f.k);
}
// ⊢ f ↔ g  (f, g は α 同値. desugar 済み)
function alphaIff(f, g) {
  if (key(f) === key(g)) return tc([], [], Iff(f, f));
  if (f.k !== g.k) throw new Error('alphaIff: 形が違う ' + show(f) + ' / ' + show(g));
  switch (f.k) {
    case 'not': return tc([], [alphaIff(f.a, g.a)], Iff(f, g));
    case 'imp': return tc([], [alphaIff(f.a, g.a), alphaIff(f.b, g.b)], Iff(f, g));
    case 'all': {
      if (f.v === g.v) {
        const c = alphaIff(f.a, g.a), v = f.v;
        const g1 = gen(tc([], [c], Imp(f.a, g.a)), v), g2 = gen(tc([], [c], Imp(g.a, f.a)), v);
        const a3 = ax('A3', Imp(All(v, Imp(f.a, g.a)), Imp(f, g))), a3b = ax('A3', Imp(All(v, Imp(g.a, f.a)), Imp(g, f)));
        return tc([], [g1, g2, a3, a3b], Iff(f, g));
      }
      const u = f.v, w = g.v;
      if (fv(g).has(u) || !C.substitutable(V(u), w, g.a)) throw new Error('alphaIff: 付け替えできない');
      const mid = All(u, subst(g.a, w, V(u)));
      return tc([], [alphaIff(f, mid), alphaImp(mid, g), alphaImp(g, mid)], Iff(f, g));
    }
  }
  throw new Error('alphaIff: 原子論理式が一致しない ' + show(f) + ' / ' + show(g));
}
// ctx ⊢ φ から ctx ⊢ φ' (α 同値)
function alphaConv(line, target) { target = P(target); return tc(line.ctx, [line, alphaIff(desugar(line.phi), desugar(target))], target); }

// ---------- 全称例化 ----------
function inst1(line, t) {
  const phi = line.phi.k === 'all' ? line.phi : desugar(line.phi);
  if (phi.k !== 'all') throw new Error('inst: ∀ でない ' + show(line.phi));
  const x = phi.v, body = phi.a; t = T(t);
  if (!C.substitutable(t, x, body)) {
    const used = new Set([...C.allVars(line.phi), ...fvT(t)]);
    const f2 = All(x, renameBound(line.phi.k === 'all' ? line.phi.a : body, fvT(t), used));
    return inst1(alphaConv(line, f2), t);
  }
  const res = subst(body, x, t);
  const a2 = mkLeaf('A2', Imp(phi, res));
  if (line.ctx.length === 0) return new Line([], res, mkMP(line.node, a2));
  return tc(line.ctx, [line, new Line([], a2.f, a2)], res);
}
// 先頭の n 個の ∀ を順に例化する. 束縛変数の捕獲が起きる場合は, まず新しい変数で
// 例化してから Gen し直して束縛変数を付け替える(∀x∀yφ ⊢ ∀x'∀y'φ').
let renameN = 0;
function inst(line, ts) {
  ts = ts.map(t => T(t));
  let phi = line.phi, ok = true;
  for (const t of ts) {
    const d = phi.k === 'all' ? phi : desugar(phi);
    if (d.k !== 'all') throw new Error('inst: ∀ でない ' + show(line.phi));
    if (!C.substitutable(t, d.v, d.a)) { ok = false; break; }
    phi = subst(d.a, d.v, t);
  }
  if (!ok) {
    const used = new Set([...C.allVars(line.phi), ...ts.flatMap(t => [...fvT(t)])]);
    for (const h of line.ctx) C.allVars(h, used);
    const vs = ts.map(() => { let v; do { v = 'v' + (++renameN); } while (used.has(v)); used.add(v); return v; });
    const l1 = vs.reduce((l, v) => inst1(l, V(v)), line);
    line = genAll(l1, vs);
  }
  return ts.reduce((l, t) => inst1(l, t), line);
}

// ---------- 存在 ----------
// line: ctx ⊢ ψ^x_t  から  ctx ⊢ ∃x ψ
function exI(line, x, psi, t) {
  psi = P(psi); t = T(t);
  const inst = subst(psi, x, t);
  if (!same(inst, line.phi)) throw new Error('exI: 行が ψ(t) でない\n  ' + show(line.phi) + '\n  ' + show(inst));
  if (!C.substitutable(t, x, psi)) throw new Error('exI: 代入可能でない');
  const a2 = mkLeaf('A2', Imp(All(x, Not(psi)), Not(inst)));
  return tc(line.ctx, [line, new Line([], a2.f, a2)], Ex(x, psi));
}
// lineEx: ctx ⊢ ∃x φ.  body(h): ctx+[φ^x_y] の行 h(仮定)を受け取り, ctx+[φ^x_y] ⊢ ψ の行を返す.
function exE(lineEx, y, body, ctxW) {
  if (ctxW && ctxW.length !== lineEx.ctx.length) lineEx = tc(ctxW, [lineEx], lineEx.phi);
  const ctx = lineEx.ctx;
  const ex = lineEx.phi.k === 'ex' ? lineEx.phi : null;
  if (!ex) throw new Error('exE: ∃ の形でない ' + show(lineEx.phi));
  const x = ex.v, phi = ex.a;
  if (!C.substitutable(V(y), x, phi)) throw new Error('exE: 変数を代入できない');
  const phiy = subst(phi, x, V(y));
  for (const h of ctx) if (fv(h).has(y)) throw new Error('exE: 固有変数 ' + y + ' が仮定に現れる');
  if (y !== x && fv(phi).has(y)) throw new Error('exE: 固有変数 ' + y + ' が φ に自由に現れる');
  const ctx2 = ctx.concat([phiy]);
  const bl = body(hyp(ctx2, ctx2.length - 1), ctx2);
  if (bl.ctx.length !== ctx2.length) throw new Error('exE: 本体の文脈が違う');
  const psi = bl.phi;
  if (fv(psi).has(y)) throw new Error('exE: 固有変数 ' + y + ' が結論に現れる: ' + show(psi));
  const K = ctx.length ? And(conj(ctx), Not(psi)) : Not(psi);
  const l1 = tc([], [bl], Imp(K, Not(phiy)));
  const g = mkGen(l1.node, y);
  const a3 = mkLeaf('A3', Imp(g.f, Imp(All(y, K), All(y, Not(phiy)))));
  const a4 = mkLeaf('A4', Imp(K, All(y, K)));
  const prems = [lineEx, new Line([], g.f, g), new Line([], a3.f, a3), new Line([], a4.f, a4)];
  if (y !== x) { // ∀y¬φ(y) → ∀x¬φ(x)
    const a2 = mkLeaf('A2', Imp(All(y, Not(phiy)), Not(phi)));
    const g2 = mkGen(a2, x);
    const a3b = mkLeaf('A3', Imp(g2.f, Imp(All(x, All(y, Not(phiy))), All(x, Not(phi)))));
    const a4b = mkLeaf('A4', Imp(All(y, Not(phiy)), All(x, All(y, Not(phiy)))));
    for (const n of [g2, a3b, a4b]) prems.push(new Line([], n.f, n));
  }
  return tc(ctx, prems, psi);
}

// ---------- 仮定の導入・解消 ----------
function assume(ctx, h, body) { // body(hLine, ctx2) が ctx2 ⊢ ψ を返す → ctx ⊢ h → ψ
  h = P(h);
  const ctx2 = ctx.concat([h]);
  const r = body(hyp(ctx2, ctx2.length - 1), ctx2);
  if (r.ctx.length !== ctx2.length) throw new Error('assume: 文脈が違う');
  return new Line(ctx, Imp(h, r.phi), r.node);
}
// 背理法: ctx+[¬θ] ⊢ ⊥ 相当 (χ と ¬χ) から ctx ⊢ θ
function raa(ctx, theta, body) {
  theta = P(theta);
  const ctx2 = ctx.concat([Not(theta)]);
  let [l1, l2] = body(hyp(ctx2, ctx2.length - 1), ctx2);
  if (l1.ctx.length !== ctx2.length) l1 = tc(ctx2, [l1], l1.phi);
  if (l2.ctx.length !== ctx2.length) l2 = tc(ctx2, [l2], l2.phi);
  return tc(ctx, [new Line(ctx, Imp(Not(theta), l1.phi), l1.node), new Line(ctx, Imp(Not(theta), l2.phi), l2.node)], theta);
}
// ctx ⊢ ¬∀yφ  から  ctx ⊢ ∃y¬φ  (∃y¬φ :≡ ¬∀y¬¬φ なので ∀y¬¬φ → ∀yφ を示す)
function notAllToEx(line) {
  const f = line.phi; if (!(f.k === 'not' && f.a.k === 'all')) throw new Error('notAllToEx: ¬∀ でない');
  const y = f.a.v, phi = f.a.a;
  const nn = All(y, Not(Not(phi)));
  const a2 = mkLeaf('A2', Imp(nn, Not(Not(phi))));
  const l1 = tc([], [new Line([], a2.f, a2)], Imp(nn, phi));
  const g = mkGen(l1.node, y);
  const a3 = mkLeaf('A3', Imp(g.f, Imp(All(y, nn), All(y, phi))));
  const a4 = mkLeaf('A4', Imp(nn, All(y, nn)));
  return tc(line.ctx, [line, new Line([], g.f, g), new Line([], a3.f, a3), new Line([], a4.f, a4)], Ex(y, Not(phi)));
}
// 文脈を広げる
const weaken = (line, ctx) => tc(ctx, [line], line.phi);

// ---------- 等号 ----------
const cache = new Map();
function logicThm(name, build) { if (!cache.has(name)) cache.set(name, build()); return cache.get(name); }
// ⊢ ∀x x = x
function reflAll() { return logicThm('refl', () => { const a5 = mkLeaf('A5', Eq(V('x'), V('x'))); return new Line([], All('x', a5.f), mkGen(a5, 'x')); }); }
function refl(t) { return inst(reflAll(), [T(t)]); }
// ⊢ ∀x∀y(x=y → y=x)
function symAll() {
  return logicThm('sym', () => {
    const a6 = ax('A6', Imp(Eq(V('x'), V('y')), Imp(Eq(V('x'), V('x')), Eq(V('y'), V('x')))));
    const a5 = ax('A5', Eq(V('x'), V('x')));
    const l = tc([], [a6, a5], Imp(Eq(V('x'), V('y')), Eq(V('y'), V('x'))));
    return genAll(l, ['x', 'y']);
  });
}
// ⊢ ∀x∀y∀z(x=y → (y=z → x=z))
function transAll() {
  return logicThm('trans', () => {
    const a6 = ax('A6', Imp(Eq(V('y'), V('z')), Imp(Eq(V('x'), V('y')), Eq(V('x'), V('z')))));
    const l = tc([], [a6], Imp(Eq(V('x'), V('y')), Imp(Eq(V('y'), V('z')), Eq(V('x'), V('z')))));
    return genAll(l, ['x', 'y', 'z']);
  });
}
function neSym(line) { // ctx ⊢ t≠u  →  ctx ⊢ u≠t
  const e = desugar(line.phi); if (!(e.k === 'not' && e.a.k === 'eq')) throw new Error('neSym: 不等式でない');
  const s = inst(symAll(), [e.a.b, e.a.a]);
  return tc(line.ctx, [line, s], Not(Eq(e.a.b, e.a.a)));
}
function sym(line) { // ctx ⊢ t=u  →  ctx ⊢ u=t
  const e = desugar(line.phi); if (e.k !== 'eq') throw new Error('sym: 等式でない');
  const s = inst(symAll(), [e.a, e.b]);
  return tc(line.ctx, [line, s], Eq(e.b, e.a));
}
function trans(l1, l2, ctx) { // t=u, u=s → t=s
  ctx = ctx ?? (l1.ctx.length >= l2.ctx.length ? l1.ctx : l2.ctx);
  const e1 = desugar(l1.phi), e2 = desugar(l2.phi);
  if (C.tkey(e1.b) !== C.tkey(e2.a)) throw new Error('trans: 中央の項が一致しない ' + show(l1.phi) + ' , ' + show(l2.phi));
  const t = inst(transAll(), [e1.a, e1.b, e2.b]);
  return tc(ctx, [l1, l2, t], Eq(e1.a, e2.b));
}
function chain(lines, ctx) { return lines.slice(1).reduce((acc, l) => trans(acc, l, ctx), lines[0]); }

// 原子論理式 α, α' について ⊢ t=u → (α → α') を作る(α' は α の t の一部を u に置き換えたもの)
let freshN = 0;
const fresh = base => base + '_{' + (++freshN) + '}';
function rwAtom(t, u, a, a2) {
  const used = new Set([...C.allVars(a), ...C.allVars(a2), ...fvT(t), ...fvT(u)]);
  let z = 'z', w = 'w', i = 0;
  while (used.has(z)) z = 'z' + (++i);
  while (used.has(w) || w === z) w = 'w' + (++i);
  // β: α の置き換え位置を z にしたもの
  function bt(s, s2) {
    if (C.tkey(s) === C.tkey(s2)) return s;
    if (C.tkey(s) === C.tkey(t) && C.tkey(s2) === C.tkey(u)) return V(z);
    if (s.k === 'app' && s2.k === 'app' && s.f === s2.f) return F(s.f, ...s.a.map((x, i) => bt(x, s2.a[i])));
    throw new Error('rw: 置き換えの形でない ' + C.showT(s) + ' / ' + C.showT(s2));
  }
  let b;
  if (a.k === 'eq') b = Eq(bt(a.a, a2.a), bt(a.b, a2.b));
  else b = Rel(a.r, ...a.a.map((s, i) => bt(s, a2.a[i])));
  const a6 = mkLeaf('A6', Imp(Eq(V(z), V(w)), Imp(b, subst(b, z, V(w)))));
  const g = genAll(new Line([], a6.f, a6), [z, w]);
  return inst(g, [t, u]);
}
// eqLine: ctx ⊢ t = u,  line: ctx ⊢ φ,  target: φ' (φ の原子部分論理式中の t の一部を u に置換)
function rw(eqLine, line, target, ctx) {
  target = P(target);
  ctx = ctx ?? (eqLine.ctx.length >= line.ctx.length ? eqLine.ctx : line.ctx);
  const e = desugar(eqLine.phi); if (e.k !== 'eq') throw new Error('rw: 等式でない');
  const t = e.a, u = e.b;
  const pairs = [];
  function walk(f, g) {
    if (f.k !== g.k) throw new Error('rw: 形が違う ' + show(f) + ' / ' + show(g));
    switch (f.k) {
      case 'eq': case 'rel':
        if (C.key(f) === C.key(g)) return;
        if (!pairs.some(([a, b]) => C.key(a) === C.key(f) && C.key(b) === C.key(g))) pairs.push([f, g]); return;
      case 'not': walk(f.a, g.a); return;
      case 'imp': walk(f.a, g.a); walk(f.b, g.b); return;
      case 'all': if (C.key(f) !== C.key(g)) throw { deep: true }; return;
    }
  }
  try { walk(desugar(line.phi), desugar(target)); } catch (ex) { if (ex && ex.deep) return rwDeep(eqLine, line, target, ctx); throw ex; }
  const fwd = pairs.map(([f, g]) => rwAtom(t, u, f, g));
  // まず前向きの補題だけで試み, 足りなければ逆向きも加える
  const prems = [eqLine, line, ...fwd];
  if (C.isTautology(prems.reduceRight((acc, p) => Imp(p.node.f, acc), curry(ctx, target)))) return tc(ctx, prems, target);
  const bwd = pairs.map(([f, g]) => rwAtom(u, t, g, f));
  return tc(ctx, [...prems, ...bwd, sym(eqLine)], target);
}


// 一般の論理式の書き換え: ⊢ t=u → (φ ↔ φ')  (φ' は φ の t の一部を u に置き換えたもの. 量化子の内側も可)
//   原子論理式は (A6) の例, ¬ と → はトートロジー, ∀ は Gen と (A3) による(論理式に関する帰納法の手続き).
function congIff(t, u, f, g) {
  const E = Eq(t, u);
  if (key(f) === key(g)) return tc([], [], Imp(E, Iff(f, f)));
  if (f.k !== g.k) throw new Error('rwDeep: 形が違う ' + show(f) + ' / ' + show(g));
  switch (f.k) {
    case 'eq': case 'rel': {
      const fw = rwAtom(t, u, f, g), bw = rwAtom(u, t, g, f), s = inst(symAll(), [t, u]);
      return tc([], [fw, bw, s], Imp(E, Iff(f, g)));
    }
    case 'not': return tc([], [congIff(t, u, f.a, g.a)], Imp(E, Iff(f, g)));
    case 'imp': return tc([], [congIff(t, u, f.a, g.a), congIff(t, u, f.b, g.b)], Imp(E, Iff(f, g)));
    case 'all': {
      if (f.v !== g.v) throw new Error('rwDeep: 束縛変数が違う');
      const v = f.v;
      if (fvT(t).has(v) || fvT(u).has(v)) throw new Error('rwDeep: 束縛変数 ' + v + ' が書き換える項に現れる');
      const c = congIff(t, u, f.a, g.a);
      const ctx = [E];
      const l1 = tc(ctx, [c], Imp(f.a, g.a)), l2 = tc(ctx, [c], Imp(g.a, f.a));
      const g1 = gen(l1, v), g2 = gen(l2, v);
      const a3 = ax('A3', Imp(All(v, Imp(f.a, g.a)), Imp(All(v, f.a), All(v, g.a))));
      const a3b = ax('A3', Imp(All(v, Imp(g.a, f.a)), Imp(All(v, g.a), All(v, f.a))));
      const r = tc(ctx, [g1, g2, a3, a3b], Iff(f, g));
      return new Line([], Imp(E, r.phi), r.node);
    }
  }
  throw new Error('rwDeep: 未対応 ' + f.k);
}
function rwDeep(eqLine, line, target, ctx) {
  target = P(target);
  ctx = ctx ?? (eqLine.ctx.length >= line.ctx.length ? eqLine.ctx : line.ctx);
  const e = desugar(eqLine.phi); if (e.k !== 'eq') throw new Error('rwDeep: 等式でない');
  const c = congIff(e.a, e.b, desugar(line.phi), desugar(target));
  return tc(ctx, [eqLine, line, c], target);
}

// ---------- 定義公理・定理の利用 ----------
// 定理(または定義公理)を項で例化し, 文脈 ctx のもとで MP できるものは MP して goal を得る
function use(src, terms, ctx, prems, goal) {
  const l = inst(src, terms.map(t => T(t)));
  return tc(ctx, [l, ...prems], goal);
}

module.exports = { alphaConv, alphaIff, renameBound, rwDeep, congIff, Line, curry, P, T, ax, axiom, defAx, thm, tc, hyp, mp, gen, genAll, inst, inst1, exI, exE, assume, raa, weaken, refl, sym, neSym, notAllToEx, trans, chain, rw, use, conj, fresh };
