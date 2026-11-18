'use strict';
// =====================================================================
//  kit.js — 定理の登録と, 代数計算のための補助関数
//  (いずれも tactics.js の補助関数の組合せで, 生成されるのは公理・MP・Gen の木)
// =====================================================================
const C = require('./core');
const L = require('./lang');
const X = require('./tactics');
const TX = require('./latex');
require('./theory'); require('./found');
const { V, F, Eq, Rel, Not, Imp, All, And, Ex, Le, same, key, desugar, show } = C;
const { parse, parseTerm } = L;
const P = X.P, T = X.T;

// ---------------- 定理の登録 ----------------
const proved = [];  // { name, label, f, node, stats }
function prove(name, stmt, label, fn, opt = {}) {
  const f = parse(stmt);
  const n0 = C.getNodeCount();
  let line;
  try { line = fn(); }
  catch (e) { e.message = `[${name}] ` + e.message; throw e; }
  if (line.ctx.length) throw new Error(`[${name}] 文脈が残っている`);
  if (!same(line.phi, f)) throw new Error(`[${name}] 結論が主張と一致しない\n  得たもの: ${show(line.phi)}\n  主張: ${show(f)}`);
  C.verify(line.node);
  C.Theory.thms.set(name, { f, status: 'P', node: line.node });
  TX.leafLabel.set('Thm:' + name, label);
  proved.push({ name, label, f, node: line.node, opt });
  return line;
}

// ---------------- t ∈ ℝ の証明 (文脈 ctx のもとで) ----------------
const memCache = new Map();
const memHooks = new Map();  // 関数記号 → (ctx, t, sub, facts) => 行
const seqHooks = new Map();  // 関数記号 g → (ctx, g(…)項, facts) => ctx ⊢ Seq(g(…))
const ctxKey = ctx => ctx.map(key).join('|');
function inCtx(ctx, f) { return ctx.some(h => same(h, f)); }
function findFact(ctx, f, facts = []) {
  f = P(f);
  for (const l of facts) if (same(l.phi, f)) return l;
  if (inCtx(ctx, f)) return X.hyp(ctx, f);
  return null;
}
function mem(ctx, t, facts = []) {
  t = T(t);
  const goal = Rel('in', t, F('Real'));
  const ck = ctxKey(ctx) + '#' + C.tkey(t);
  const hit = findFact(ctx, goal, facts);
  if (hit) return hit;
  if (memCache.has(ck)) return memCache.get(ck);
  let r;
  const sub = s => mem(ctx, s, facts);
  if (t.k === 'var') throw new Error('mem: ' + t.n + ' ∈ ℝ が文脈にない');
  switch (t.f) {
    case '0': r = X.thm('R1_0'); break;
    case '1': r = X.thm('R1_1'); break;
    case '2': r = X.thm('TwoR'); break;
    case '+': r = X.tc(ctx, [X.inst(X.thm('R1_add'), t.a), sub(t.a[0]), sub(t.a[1])], goal); break;
    case '*': r = X.tc(ctx, [X.inst(X.thm('R1_mul'), t.a), sub(t.a[0]), sub(t.a[1])], goal); break;
    case 'neg': r = X.tc(ctx, [X.inst(X.thm('R1_neg'), t.a), sub(t.a[0])], goal); break;
    case '-': r = X.tc(ctx, [X.inst(X.thm('SubR'), t.a), sub(t.a[0]), sub(t.a[1])], goal); break;
    case 'inv': {
      if (t.a[0].k === 'app' && t.a[0].f === '2') { r = X.thm('InvTwoR'); break; }
      const nz = findFact(ctx, Not(Eq(t.a[0], F('0'))), facts);
      if (!nz) throw new Error('mem: ' + C.showT(t.a[0]) + ' ≠ 0 が必要');
      r = X.tc(ctx, [X.inst(X.thm('R1_inv'), t.a), sub(t.a[0]), nz], goal); break;
    }
    case 'abs': r = X.tc(ctx, [X.inst(X.thm('AbsR'), t.a), sub(t.a[0])], goal); break;
    case 'iota': {
      const nn = findFact(ctx, Rel('in', t.a[0], F('Nat')), facts);
      if (!nn) throw new Error('mem: ' + C.showT(t.a[0]) + ' ∈ ℕ が必要');
      r = X.tc(ctx, [X.inst(X.thm('IotaR'), t.a), nn], goal); break;
    }
    case 'app': {
      const [a, n] = t.a;
      let sq = findFact(ctx, Rel('Seq', a), facts);
      if (!sq && a.k === 'app' && seqHooks.has(a.f)) sq = seqHooks.get(a.f)(ctx, a, facts);
      if (sq) {
        const nn = findFact(ctx, Rel('in', n, F('Nat')), facts);
        if (!nn) throw new Error('mem: ' + C.showT(n) + ' ∈ ℕ が必要');
        r = X.tc(ctx, [X.inst(X.thm('SeqVal'), t.a), sq, nn], goal); break;
      }
      const rf = findFact(ctx, Rel('RFn', a), facts);
      const dm = findFact(ctx, Rel('in', n, F('dom', a)), facts);
      if (!rf || !dm) throw new Error('mem: ' + C.showT(t) + ' の値が実数であることを示せない');
      r = X.tc(ctx, [X.inst(X.thm('RFnVal'), t.a), rf, dm], goal); break;
    }
    default:
      if (memHooks.has(t.f)) { r = memHooks.get(t.f)(ctx, t, sub, facts); break; }
      throw new Error('mem: 未対応の項 ' + C.showT(t));
  }
  memCache.set(ck, r);
  return r;
}

// ---------------- 定理の例化と前件の解消 ----------------
// src(定理名または行)を terms で例化し, 前件を順に解消する.
//   前件が "t ∈ ℝ" なら mem で, それ以外は facts または ctx の仮定から.
//   解消できない前件が現れたらそこで止める.
function use(name, terms, ctx, facts = []) {
  let l = typeof name === 'string' ? X.thm(name) : name;
  l = X.inst(l, terms.map(t => T(t)));
  const supplied = [];
  let phi = l.phi;
  for (;;) {
    let a, b;
    if (phi.k === 'imp') { a = phi.a; b = phi.b; }
    else break;
    let s = null;
    const da = desugar(a);
    if (da.k === 'rel' && da.r === 'in' && da.a[1].k === 'app' && da.a[1].f === 'Real' && a.k === 'rel') { try { s = mem(ctx, da.a[0], facts); } catch (e) { s = null; } }
    if (!s) s = findFact(ctx, a, facts);
    if (!s) break;
    supplied.push(s); phi = b;
  }
  if (!supplied.length) return l.ctx.length ? l : l;
  return X.tc(ctx, [l, ...supplied], phi);
}

// ---------------- 等式 ----------------
// eq: ctx ⊢ s = s'.  term T の中の s の(すべての)出現を s' に置き換えた T' について ctx ⊢ T = T'.
function replaceTerm(t, s, s2) {
  if (C.tkey(t) === C.tkey(s)) return s2;
  if (t.k === 'var') return t;
  return F(t.f, ...t.a.map(u => replaceTerm(u, s, s2)));
}
function cong(eq, term, ctx) {
  term = T(term); ctx = ctx ?? eq.ctx;
  const e = desugar(eq.phi);
  const target = replaceTerm(term, e.a, e.b);
  const r = X.refl(term);
  return X.rw(eq, r, Eq(term, target), ctx);
}
// t0 から始まる等式の連鎖. steps: [ [to, line], ... ]
//   line が cur = to / to = cur の等式ならそのまま, そうでなければ s = s' による部分項の書き換え.
function calc(ctx, t0, steps) {
  let cur = T(t0); const lines = [];
  for (const [toS, by] of steps) {
    const to = T(toS);
    const e = desugar(by.phi);
    let l;
    if (e.k === 'eq' && C.tkey(e.a) === C.tkey(cur) && C.tkey(e.b) === C.tkey(to)) l = by;
    else if (e.k === 'eq' && C.tkey(e.b) === C.tkey(cur) && C.tkey(e.a) === C.tkey(to)) l = X.sym(by);
    else {
      // cur の中の s の一部を s' に置き換えると to になる(どの出現かは A6 の補題が判定する)
      const goal = Eq(cur, to);
      try { l = X.rw(by, X.refl(cur), goal, ctx); }
      catch (e1) {
        try { l = X.rw(X.sym(by), X.refl(cur), goal, ctx); }
        catch (e2) { throw new Error('calc: ' + C.showT(cur) + ' から ' + C.showT(to) + ' へ ' + show(by.phi) + ' で書き換えられない'); }
      }
    }
    lines.push(l); cur = to;
  }
  return X.chain(lines, ctx);
}
// 論理式 line (ctx ⊢ φ) の中の項を等式で書き換える
function rewrite(eq, line, target, ctx) { return X.rw(eq, line, P(target), ctx ?? line.ctx); }

// ∀v1…∀vk (v1∈ℝ → … → vk∈ℝ → h1 → … → hm → φ) の形の定理を証明する.
//   body(ctx, hyps) は ctx ⊢ φ の行を返す (hyps は h1…hm の仮定の行).
function intro(vars, hyps, body, opts = {}) {
  const real = opts.notReal ? [] : vars.map(v => v + ' in Real');
  const hs = [...real, ...hyps].map(h => P(h));
  function rec(i, ctx) {
    if (i === hs.length) return body(ctx, ctx.slice(real.length).map((h, j) => X.hyp(ctx, real.length + j)));
    return X.assume(ctx, hs[i], (hl, c2) => rec(i + 1, c2));
  }
  return X.genAll(rec(0, []), vars);
}
// 場合分け: ctx ⊢ A ∨ B (または A ∨ B ∨ C) の行と, 各場合の結論 → ctx ⊢ goal
function cases(ctx, disj, caseFns, goal) {
  goal = P(goal);
  const parts = [];
  (function split(f) { if (f.k === 'or') { split(f.a); split(f.b); } else parts.push(f); })(disj.phi);
  if (parts.length !== caseFns.length) throw new Error('cases: 場合の数が違う');
  const ls = parts.map((p, i) => X.assume(ctx, p, (h, c2) => caseFns[i](h, c2)));
  return X.tc(ctx, [disj, ...ls], goal);
}

module.exports = { seqHooks, memHooks, intro, cases, prove, proved, mem, use, cong, calc, rewrite, findFact, replaceTerm, X, C, L, TX, P, T, parse, parseTerm, V, F, Eq, Rel, Not, Imp, All, And, Ex, Le, same, show };
