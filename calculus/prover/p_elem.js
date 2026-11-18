'use strict';
// テキスト第4章 3節: 初等関数 (指数関数・対数関数; 定義3.1)
const K = require('./kit');
const { X, C, prove, use, calc, mem, P, T } = K;
const { fthm } = require('./theory');
const L = require('./lang');
require('./p_inv');

// ---------------- 記号 ----------------
L.defFunc('exp', 0, () => '\\exp');
const finvTex = L.funcs.get('finv').tex;
L.funcs.get('finv').tex = a => (a[0] === '\\exp' ? '\\log' : finvTex(a));
// 指数関数の存在 (基礎定理. 通常の証明は本文: 冪級数による構成)
fthm('Exp', 'RFn(exp) & dom(exp) = Real & (all x. (x in Real -> 0 < exp[x])) & (all x. all y. (x in Real -> y in Real -> exp[x + y] = exp[x] * exp[y])) & StrInc(exp, Real) & ContOn(exp, Real) & all y. (y in Real -> 0 < y -> ex x. (x in Real & exp[x] = y))', '[S27]', '指数関数');
const LG = 'finv(exp)';
const ex = (s) => X.tc([], [X.thm('Exp')], s);

prove('ItvReal', 'Itv(Real)', '[I5]', () => {
  const all = X.genAll(X.assume([], 'x in Real', (h1, c1) => X.assume(c1, 'z in Real', (h2, c2) => X.assume(c2, 'y in Real', (h3, c3) =>
    X.assume(c3, 'x <= y', (h4, c4) => X.assume(c4, 'y <= z', (h5, c5) => X.weaken(h3, c5)))))), ['x', 'y', 'z']);
  return X.tc([], [X.inst(X.defAx('Itv'), [T('Real')]), X.inst(X.thm('SubRefl'), [T('Real')]), all], 'Itv(Real)');
});

// exp に関する準備: dom(exp) = ℝ による書き換え
function expFacts(c) {
  const dE = ex('dom(exp) = Real');
  const hR = ex('RFn(exp)');
  const hI = X.rw(X.sym(dE), X.thm('ItvReal'), 'Itv(dom(exp))', []);
  const s0 = ex('StrInc(exp, Real)');
  const hS = X.rw(X.sym(dE), s0, 'StrInc(exp, dom(exp))', []);
  const inv = use('InvFn', ['exp'], c, [hR, use('StrIncInj', ['exp'], c, [hR, hS])]);
  return { dE, hR, hI, hS, inv };
}

prove('LogCont', `ContOn(${LG}, dom(${LG})) & StrInc(${LG}, dom(${LG}))`, '定理(対数関数の連続性・単調性)', () => {
  const { hR, hI, hS } = expFacts([]);
  return X.tc([], [use('InvCont', ['exp'], [], [hR, hI, hS]), use('InvMono', ['exp'], [], [hR, hS])], `ContOn(${LG}, dom(${LG})) & StrInc(${LG}, dom(${LG}))`);
});

prove('LogDom', `all y. (y in dom(${LG}) <-> y in Real & 0 < y)`, '定理(対数関数の定義域)', () => {
  const { dE, inv } = expFacts([]);
  const iff = y => X.inst(X.tc([], [inv], `all y. (y in dom(${LG}) <-> ex x. (x in dom(exp) & y = exp[x]))`), [T(y)]);
  const fw = X.assume([], `y in dom(${LG})`, (hy, c) => X.exE(X.tc(c, [iff('y'), hy], 'ex x. (x in dom(exp) & y = exp[x])'), 'x', (hx, cx) => {
    const xr = X.rw(dE, X.tc(cx, [hx], 'x in dom(exp)'), 'x in Real', cx);
    const e = X.tc(cx, [hx], 'y = exp[x]');
    const pos = X.tc(cx, [X.inst(ex('all x. (x in Real -> 0 < exp[x])'), [T('x')]), xr], '0 < exp[x]');
    const er = X.tc(cx, [X.inst(X.thm('RFnVal'), [T('exp'), T('x')]), ex('RFn(exp)'), X.tc(cx, [hx], 'x in dom(exp)')], 'exp[x] in Real');
    return X.rw(X.sym(e), X.tc(cx, [er, pos], 'exp[x] in Real & 0 < exp[x]'), 'y in Real & 0 < y', cx);
  }, c));
  const bw = X.assume([], 'y in Real & 0 < y', (hy, c) => X.exE(X.tc(c, [X.inst(ex('all y. (y in Real -> 0 < y -> ex x. (x in Real & exp[x] = y))'), [T('y')]), hy], 'ex x. (x in Real & exp[x] = y)'), 'x', (hx, cx) => {
    const xd = X.rw(X.sym(dE), X.tc(cx, [hx], 'x in Real'), 'x in dom(exp)', cx);
    const w = X.exI(X.tc(cx, [xd, X.sym(X.tc(cx, [hx], 'exp[x] = y'))], 'x in dom(exp) & y = exp[x]'), 'x', 'x in dom(exp) & y = exp[x]', 'x');
    return X.tc(cx, [iff('y'), w], `y in dom(${LG})`);
  }, c));
  return X.gen(X.tc([], [fw, bw], `y in dom(${LG}) <-> y in Real & 0 < y`), 'y');
});

prove('LogMul', `all x. all y. (x in dom(${LG}) -> y in dom(${LG}) -> ${LG}[x * y] = ${LG}[x] + ${LG}[y])`, '定理(対数法則)', () => {
  const { dE, inv } = expFacts([]);
  const at = (c, y, hy) => {
    const l = X.tc(c, [X.inst(X.tc(c, [inv], `all y. (y in dom(${LG}) -> ${LG}[y] in dom(exp) & exp[${LG}[y]] = y)`), [T(y)]), hy], `${LG}[${y}] in dom(exp) & exp[${LG}[${y}]] = ${y}`);
    const d = X.tc(c, [l], `${LG}[${y}] in dom(exp)`);
    return [d, X.rw(dE, d, `${LG}[${y}] in Real`, c), X.tc(c, [l], `exp[${LG}[${y}]] = ${y}`)];
  };
  return X.genAll(X.assume([], `x in dom(${LG})`, (hx, c1) => X.assume(c1, `y in dom(${LG})`, (hy, c) => {
    const a = `${LG}[x]`, b = `${LG}[y]`;
    const [, ar, ea] = at(c, 'x', hx), [, br, eb] = at(c, 'y', hy);
    const add = X.tc(c, [X.inst(ex('all x. all y. (x in Real -> y in Real -> exp[x + y] = exp[x] * exp[y])'), [T(a), T(b)]), ar, br], `exp[${a} + ${b}] = exp[${a}] * exp[${b}]`);
    const e1 = calc(c, `exp[${a} + ${b}]`, [[`exp[${a}] * exp[${b}]`, add], [`x * exp[${b}]`, ea], ['x * y', eb]]);
    const sd = X.rw(X.sym(dE), mem(c, `${a} + ${b}`, [ar, br]), `${a} + ${b} in dom(exp)`, c);
    const g = X.tc(c, [X.inst(X.tc(c, [inv], `all x. (x in dom(exp) -> ${LG}[exp[x]] = x)`), [T(`${a} + ${b}`)]), sd], `${LG}[exp[${a} + ${b}]] = ${a} + ${b}`);
    return X.rw(e1, g, `${LG}[x * y] = ${a} + ${b}`, c);
  })), ['x', 'y']);
});
