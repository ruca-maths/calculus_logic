'use strict';
// テキスト第4章 2節 定理2.4 と 4節: 一様連続性 (定義4.1, 定理4.3, 4.6)
const K = require('./kit');
const { X, C, prove, intro, use, calc, mem, P, T } = K;
const { def } = require('./theory');
const { CE, cinDef, subE, coDef } = require('./p_cont');
const { convIntro, tailIntro, tailAt } = require('./p_seq');
const { ccInst } = require('./p_fun');
require('./p_ivt');

// ---------------- 補題 ----------------
prove('AbsLtBoth', 'all x. all c. all d. (x in Real -> c in Real -> d in Real -> abs(x - c) < d -> c - d < x & x < c + d)', '[E46]', () => intro(['x', 'c', 'd'], ['abs(x - c) < d'], (k, [h]) => {
  const b = use('AbsLt', ['x - c', 'd'], k, [h]);
  const up = X.rw(use('R3', ['d', 'c'], k), use('LtSubAdd', ['x', 'c', 'd'], k, [X.tc(k, [b], 'x - c < d')]), 'x < c + d', k);
  const l = use('R14', ['-d', 'x - c', 'c'], k, [X.tc(k, [b], '-d < x - c')]);
  const e = X.trans(use('R3', ['-d', 'c'], k), X.sym(X.inst(X.defAx('minus'), ['c', 'd'])), k);
  const lo = X.rw(use('SubAdd', ['x', 'c'], k), X.rw(e, l, 'c - d < (x - c) + c', k), 'c - d < x', k);
  return X.tc(k, [lo, up], 'c - d < x & x < c + d');
}));
prove('RightAbsLe', 'all x. all c. all d. (x in Real -> c in Real -> d in Real -> c <= x -> x < c + d -> abs(x - c) < d)', '[E47]', () => intro(['x', 'c', 'd'], ['c <= x', 'x < c + d'], (k, [h1, h2]) => {
  const ab = use('AbsOfNonneg', ['x - c'], k, [use('SubNonneg', ['c', 'x'], k, [h1])]);
  return X.rw(X.sym(ab), use('LtAddSwap', ['c', 'd', 'x'], k, [h2]), 'abs(x - c) < d', k);
}));

// ---------------- 定理 2.4: 連続 ⇔ 右連続かつ左連続 ----------------
prove('ContRL', 'all f. all c. (Cont(f,c) <-> RCont(f,c) & LCont(f,c))', '定理2.4', () => X.genAll((() => {
  const dC = X.inst(X.defAx('Cont'), ['f', 'c']), dI = cinDef('f', 'dom(f)', 'c');
  const dR = X.inst(X.defAx('RCont'), ['f', 'c']), dL = X.inst(X.defAx('LCont'), ['f', 'c']);
  const EP = (cond) => `ex de. (de in Real & 0 < de & all x. (x in dom(f) -> ${cond} -> abs(f[x] - f[c]) < eps))`;
  const condR = 'c <= x -> x < c + de', condL = 'c - de < x -> x <= c';
  const fw = X.assume([], 'Cont(f,c)', (h, k) => {
    const rf = X.tc(k, [h, dC, dI], 'RFn(f)'), cd = X.tc(k, [h, dC, dI], 'c in dom(f)');
    const cr = use('RFnDom', ['f', 'c'], k, [rf, cd]);
    const epsC = X.tc(k, [h, dC, dI], `all eps. (eps in Real -> 0 < eps -> ${CE('dom(f)', 'c', 'eps')})`);
    const side = (cond, lemma) => X.gen(X.assume(k, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => X.exE(X.tc(c2, [X.inst(epsC, ['eps']), he, hp], CE('dom(f)', 'c', 'eps')), 'de', (hd, cdd) => {
      const der = X.tc(cdd, [hd], 'de in Real');
      const [p1, p2] = cond.split(' -> ');
      const all = X.gen(X.assume(cdd, 'x in dom(f)', (hx, d1) => X.assume(d1, p1, (h1, d2) => X.assume(d2, p2, (h2, d3) => {
        const xr = use('RFnDom', ['f', 'x'], d3, [rf, hx]);
        const ab = lemma === 'R' ? use('RightAbsLe', ['x', 'c', 'de'], d3, [xr, cr, der, h1, h2]) : use('LeftAbsLe', ['x', 'c', 'de'], d3, [xr, cr, der, h2, h1]);
        return X.tc(d3, [X.inst(X.tc(d3, [hd], 'all x. (x in dom(f) -> abs(x - c) < de -> abs(f[x] - f[c]) < eps)'), ['x']), hx, ab], 'abs(f[x] - f[c]) < eps');
      }))), 'x');
      const G = EP(cond).replace(/^ex de\. \(/, '').replace(/\)$/, '');
      return X.exI(X.tc(cdd, [hd, all], G), 'de', G, 'de');
    }, c2))), 'eps');
    return X.tc(k, [dR, dL, rf, cd, side(condR, 'R'), side(condL, 'L')], 'RCont(f,c) & LCont(f,c)');
  });
  const bw = X.assume([], 'RCont(f,c) & LCont(f,c)', (h, k) => {
    const rf = X.tc(k, [h, dR], 'RFn(f)'), cd = X.tc(k, [h, dR], 'c in dom(f)');
    const cr = use('RFnDom', ['f', 'c'], k, [rf, cd]);
    const eR = X.tc(k, [h, dR], `all eps. (eps in Real -> 0 < eps -> ${EP(condR)})`), eL = X.tc(k, [h, dL], `all eps. (eps in Real -> 0 < eps -> ${EP(condL)})`);
    const eps = X.gen(X.assume(k, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) =>
      X.exE(X.tc(c2, [X.inst(eR, ['eps']), he, hp], EP(condR)), 'd1', (q1, e1) => X.exE(X.tc(e1, [X.inst(eL, ['eps']), he, hp], EP(condL)), 'd2', (q2, e2) => {
        const d1r = X.tc(e2, [q1], 'd1 in Real'), d2r = X.tc(e2, [q2], 'd2 in Real');
        return X.exE(use('MinPos', ['d1', 'd2'], e2, [d1r, d2r, X.tc(e2, [q1], '0 < d1'), X.tc(e2, [q2], '0 < d2')]), 'de', (hd, cd2) => {
          const all = X.gen(X.assume(cd2, 'x in dom(f)', (hx, d1) => X.assume(d1, 'abs(x - c) < de', (hl, d2) => {
            const xr = use('RFnDom', ['f', 'x'], d2, [rf, hx]);
            const r1 = use('AbsLtBoth', ['x', 'c', 'd1'], d2, [xr, cr, d1r, use('LtLeTrans', ['abs(x - c)', 'de', 'd1'], d2, [hl, X.tc(d2, [hd], 'de <= d1')])]);
            const r2 = use('AbsLtBoth', ['x', 'c', 'd2'], d2, [xr, cr, d2r, use('LtLeTrans', ['abs(x - c)', 'de', 'd2'], d2, [hl, X.tc(d2, [hd], 'de <= d2')])]);
            const R = X.inst(X.tc(d2, [q1], 'all x. (x in dom(f) -> c <= x -> x < c + d1 -> abs(f[x] - f[c]) < eps)'), ['x']);
            const Lf = X.inst(X.tc(d2, [q2], 'all x. (x in dom(f) -> c - d2 < x -> x <= c -> abs(f[x] - f[c]) < eps)'), ['x']);
            return X.tc(d2, [use('R13', ['x', 'c'], d2, [xr, cr]), R, Lf, hx, r1, r2], 'abs(f[x] - f[c]) < eps');
          })), 'x');
          const G = 'de in Real & 0 < de & all x. (x in dom(f) -> abs(x - c) < de -> abs(f[x] - f[c]) < eps)';
          return X.exI(X.tc(cd2, [hd, all], G), 'de', G, 'de');
        }, e2);
      }, e1), c2))), 'eps');
    return X.tc(k, [dC, dI, rf, X.inst(X.thm('SubRefl'), ['dom(f)']), cd, eps], 'Cont(f,c)');
  });
  return X.tc([], [fw, bw], 'Cont(f,c) <-> RCont(f,c) & LCont(f,c)');
})(), ['f', 'c']));

// ---------------- 定義 4.1: 一様連続 ----------------
const UE = (F, e) => `ex de. (de in Real & 0 < de & all x. all y. (x in A -> y in A -> abs(x - y) < de -> abs(${F}[x] - ${F}[y]) < ${e}))`;
def('UC', `all f. all A. (UC(f,A) <-> RFn(f) & A sub dom(f) & all eps. (eps in Real -> 0 < eps -> ${UE('f', 'eps')}))`, 'DefUC');
const ucDef = (f, A) => X.inst(X.defAx('UC'), [f, A]);
const ucE = (c, h, F, e, he, hp) => X.tc(c, [X.inst(X.tc(c, [h, ucDef(F, 'A')], `all eps. (eps in Real -> 0 < eps -> ${UE(F, 'eps')})`), [e]), he, hp], UE(F, e));

// ---------------- 定理 4.3 ----------------
prove('UCAdd', 'all f. all g. all A. (UC(f,A) -> UC(g,A) -> UC(fadd(f,g), A))', '定理4.3(和)', () => X.genAll(
  X.assume([], 'UC(f,A)', (hf, k1) => X.assume(k1, 'UC(g,A)', (hg, k) => {
    const F = 'fadd(f,g)';
    const rf = X.tc(k, [hf, ucDef('f', 'A')], 'RFn(f)'), rg = X.tc(k, [hg, ucDef('g', 'A')], 'RFn(g)');
    const Af = X.tc(k, [hf, ucDef('f', 'A')], 'A sub dom(f)'), Ag = X.tc(k, [hg, ucDef('g', 'A')], 'A sub dom(g)');
    const FA = use('FAdd', ['f', 'g'], k, [rf, rg]);
    const domIff = X.tc(k, [FA], `all x. (x in dom(${F}) <-> x in dom(f) & x in dom(g))`);
    const valF = X.tc(k, [FA], `all x. (x in dom(${F}) -> ${F}[x] = f[x] + g[x])`);
    const inD = (cc, x, hx) => X.tc(cc, [subE(cc, Af, 'A', 'dom(f)', x, hx), subE(cc, Ag, 'A', 'dom(g)', x, hx), X.inst(domIff, [x])], `${x} in dom(${F})`);
    const sub = X.tc(k, [X.inst(X.defAx('sub'), ['A', `dom(${F})`]), X.gen(X.assume(k, 'u in A', (hu, cu) => inD(cu, 'u', hu)), 'u')], `A sub dom(${F})`);
    const eps = X.gen(X.assume(k, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => {
      const e = 'eps * 2^-1';
      const er = mem(c2, e, [he]), ep = use('HalfPos', ['eps'], c2, [he, hp]);
      return X.exE(ucE(c2, hf, 'f', e, er, ep), 'd1', (q1, e1) => X.exE(ucE(e1, hg, 'g', e, er, ep), 'd2', (q2, e2) => {
        const d1r = X.tc(e2, [q1], 'd1 in Real'), d2r = X.tc(e2, [q2], 'd2 in Real');
        return X.exE(use('MinPos', ['d1', 'd2'], e2, [d1r, d2r, X.tc(e2, [q1], '0 < d1'), X.tc(e2, [q2], '0 < d2')]), 'de', (hd, cd) => {
          const all = X.gen(X.gen(X.assume(cd, 'x in A', (hx, d1) => X.assume(d1, 'y in A', (hy, d2) => X.assume(d2, 'abs(x - y) < de', (hl, d3) => {
            const a = X.tc(d3, [X.inst(X.tc(d3, [q1], `all x. all y. (x in A -> y in A -> abs(x - y) < d1 -> abs(f[x] - f[y]) < ${e})`), ['x', 'y']), hx, hy, use('LtLeTrans', ['abs(x - y)', 'de', 'd1'], d3, [hl, X.tc(d3, [hd], 'de <= d1')])], `abs(f[x] - f[y]) < ${e}`);
            const b = X.tc(d3, [X.inst(X.tc(d3, [q2], `all x. all y. (x in A -> y in A -> abs(x - y) < d2 -> abs(g[x] - g[y]) < ${e})`), ['x', 'y']), hx, hy, use('LtLeTrans', ['abs(x - y)', 'de', 'd2'], d3, [hl, X.tc(d3, [hd], 'de <= d2')])], `abs(g[x] - g[y]) < ${e}`);
            const fr = t => mem(d3, `f[${t}]`, [rf, subE(d3, Af, 'A', 'dom(f)', t, t === 'x' ? hx : hy)]);
            const gr = t => mem(d3, `g[${t}]`, [rg, subE(d3, Ag, 'A', 'dom(g)', t, t === 'x' ? hx : hy)]);
            const s = use('ErrSum', ['f[x]', 'g[x]', 'f[y]', 'g[y]', e], d3, [fr('x'), gr('x'), fr('y'), gr('y'), er, a, b]);
            const s1 = X.rw(use('HalfSum', ['eps'], d3, [he]), s, 'abs((f[x] + g[x]) - (f[y] + g[y])) < eps', d3);
            const vx = X.tc(d3, [X.inst(valF, ['x']), inD(d3, 'x', hx)], `${F}[x] = f[x] + g[x]`), vy = X.tc(d3, [X.inst(valF, ['y']), inD(d3, 'y', hy)], `${F}[y] = f[y] + g[y]`);
            return X.rw(X.sym(vy), X.rw(X.sym(vx), s1, `abs(${F}[x] - (f[y] + g[y])) < eps`, d3), `abs(${F}[x] - ${F}[y]) < eps`, d3);
          }))), 'y'), 'x');
          const G = UE(F, 'eps').replace(/^ex de\. \(/, '').replace(/\)$/, '');
          return X.exI(X.tc(cd, [hd, all], G), 'de', G, 'de');
        }, e2);
      }, e1), c2);
    })), 'eps');
    return X.tc(k, [ucDef(F, 'A'), X.tc(k, [FA], `RFn(${F})`), sub, eps], `UC(${F}, A)`);
  })), ['f', 'g', 'A']));

prove('UCScal', 'all l. all f. all A. (l in Real -> UC(f,A) -> UC(fscal(l,f), A))', '定理4.3(定数倍)', () => X.genAll(
  X.assume([], 'l in Real', (hl0, k1) => X.assume(k1, 'UC(f,A)', (hf, k) => {
    const F = 'fscal(l,f)';
    const rf = X.tc(k, [hf, ucDef('f', 'A')], 'RFn(f)'), Af = X.tc(k, [hf, ucDef('f', 'A')], 'A sub dom(f)');
    const FS = use('FScal', ['l', 'f'], k, [hl0, rf]);
    const domIff = X.tc(k, [FS], `all x. (x in dom(${F}) <-> x in dom(f))`);
    const valF = X.tc(k, [FS], `all x. (x in dom(${F}) -> ${F}[x] = l * f[x])`);
    const inD = (cc, x, hx) => X.tc(cc, [subE(cc, Af, 'A', 'dom(f)', x, hx), X.inst(domIff, [x])], `${x} in dom(${F})`);
    const sub = X.tc(k, [X.inst(X.defAx('sub'), ['A', `dom(${F})`]), X.gen(X.assume(k, 'u in A', (hu, cu) => inD(cu, 'u', hu)), 'u')], `A sub dom(${F})`);
    const L1 = 'abs(l) + 1';
    const lp = use('LeLtTrans', ['0', 'abs(l)', L1], k, [use('AbsNonneg', ['l'], k, [hl0]), use('LtAddOne', ['abs(l)'], k, [hl0])]);
    const ln = X.neSym(use('LtNe', ['0', L1], k, [lp]));
    const eps = X.gen(X.assume(k, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => {
      const e = `(eps * (${L1})^-1)`;
      const g = [hl0, he, ln];
      const er = mem(c2, e, g), ep = use('R15', ['eps', `(${L1})^-1`], c2, [...g, hp, use('InvPos', [L1], c2, [...g, lp])]);
      return X.exE(ucE(c2, hf, 'f', e, er, ep), 'de', (hd, cd) => {
        const all = X.gen(X.gen(X.assume(cd, 'x in A', (hx, d1) => X.assume(d1, 'y in A', (hy, d2) => X.assume(d2, 'abs(x - y) < de', (hl, d3) => {
          const a = X.tc(d3, [X.inst(X.tc(d3, [hd], `all x. all y. (x in A -> y in A -> abs(x - y) < de -> abs(f[x] - f[y]) < ${e})`), ['x', 'y']), hx, hy, hl], `abs(f[x] - f[y]) < ${e}`);
          const fr = (t, h) => mem(d3, `f[${t}]`, [rf, subE(d3, Af, 'A', 'dom(f)', t, h)]);
          const gg = [...g, fr('x', hx), fr('y', hy)];
          const D = 'abs(f[x] - f[y])';
          const eq = calc(d3, 'abs(l * f[x] - l * f[y])', [['abs(l * (f[x] - f[y]))', use('MulSub', ['l', 'f[x]', 'f[y]'], d3, gg)], [`abs(l) * ${D}`, use('AbsMul', ['l', 'f[x] - f[y]'], d3, gg)]]);
          const le = use('MulLeNonneg', ['abs(l)', L1, D], d3, [...gg, use('AbsNonneg', ['f[x] - f[y]'], d3, gg), X.tc(d3, [use('LtAddOne', ['abs(l)'], d3, gg)], `abs(l) <= ${L1}`)]);
          const lt = use('MulLtPosL', [D, e, L1], d3, [...gg, lp, a]);
          const simp = calc(d3, `(${L1}) * ${e}`, [[`${e} * (${L1})`, use('R7', [L1, e], d3, gg)], ['eps', use('DivMul', ['eps', L1], d3, gg)]]);
          const r = use('LeLtTrans', [`abs(l) * ${D}`, `(${L1}) * ${D}`, 'eps'], d3, [le, X.rw(simp, lt, `(${L1}) * ${D} < eps`, d3)]);
          const r1 = X.rw(X.sym(eq), r, 'abs(l * f[x] - l * f[y]) < eps', d3);
          const vx = X.tc(d3, [X.inst(valF, ['x']), inD(d3, 'x', hx)], `${F}[x] = l * f[x]`), vy = X.tc(d3, [X.inst(valF, ['y']), inD(d3, 'y', hy)], `${F}[y] = l * f[y]`);
          return X.rw(X.sym(vy), X.rw(X.sym(vx), r1, `abs(${F}[x] - l * f[y]) < eps`, d3), `abs(${F}[x] - ${F}[y]) < eps`, d3);
        }))), 'y'), 'x');
        const G = UE(F, 'eps').replace(/^ex de\. \(/, '').replace(/\)$/, '');
        return X.exI(X.tc(cd, [hd, all], G), 'de', G, 'de');
      }, c2);
    })), 'eps');
    return X.tc(k, [ucDef(F, 'A'), X.tc(k, [FS], `RFn(${F})`), sub, eps], `UC(${F}, A)`);
  })), ['l', 'f', 'A']));

// ---------------- 定理 4.6: 有界閉区間上の連続関数は一様連続 ----------------
const I = 'cint(a,b)';
const PS1 = `x in ${I} & (ex y. (y in ${I} & abs(x - y) < iota(k)^-1 & ~ abs(f[x] - f[y]) < e0))`;
const PS2 = `x in ${I} & abs(p[k] - x) < iota(k)^-1 & ~ abs(f[p[k]] - f[x]) < e0`;
const cc1 = ccInst(PS1), cc2 = ccInst(PS2);
// 区間内の数列 u と添字列 s, 収束先 c について f∘(u∘s) → f(c)
function imageConv(cc, rf, Isub, allC, u, su, hu, si, cI, conv) {
  const ns = X.tc(cc, [si, X.inst(X.defAx('SubIdx'), ['s'])], 'NSeq(s)');
  const ss = use('SubSeqF', [u, 's'], cc, [su, ns]);
  const S = `sseq(${u},s)`;
  const val = (cn, n, hn) => X.tc(cn, [X.inst(X.tc(cn, [ss], `all k. (k in Nat -> ${S}[k] = ${u}[s[k]])`), [n]), hn], `${S}[${n}] = ${u}[s[${n}]]`);
  const inI = X.gen(X.assume(cc, 'n in Nat', (hn, cn) => X.rw(X.sym(val(cn, 'n', hn)), X.tc(cn, [X.inst(hu, ['s[n]']), use('NSeqVal', ['s', 'n'], cn, [ns, hn])], `${u}[s[n]] in ${I}`), `${S}[n] in ${I}`, cn)), 'n');
  const ci = X.tc(cc, [X.inst(allC, ['c']), cI], `ContIn(f, ${I}, c)`);
  const fc = use('ContInSeq', ['f', I, 'c', S], cc, [ci, X.tc(cc, [ss], `Seq(${S})`), inI, conv]);
  const dom1 = X.gen(X.assume(cc, 'n in Nat', (hn, cn) => subE(cn, Isub, I, 'dom(f)', `${S}[n]`, X.tc(cn, [X.inst(inI, ['n']), hn], `${S}[n] in ${I}`))), 'n');
  const cs = use('CompSeq', ['f', S], cc, [rf, X.tc(cc, [ss], `Seq(${S})`), dom1]);
  const fval = (cn, n, hn) => X.trans(X.tc(cn, [X.inst(X.tc(cn, [cs], `all n. (n in Nat -> compseq(f,${S})[n] = f[${S}[n]])`), [n]), hn], `compseq(f,${S})[${n}] = f[${S}[${n}]]`),
    K.cong(val(cn, n, hn), `f[${S}[${n}]]`, cn), cn);
  return { fc, fval, val, ns, ss };
}
prove('HeineCantor', `all f. all a. all b. (ContOn(f, ${I}) -> a in Real -> b in Real -> UC(f, ${I}))`, '定理4.6', () => X.genAll(
  X.assume([], `ContOn(f, ${I})`, (hco, k1) => X.assume(k1, 'a in Real', (ar, k2) => X.assume(k2, 'b in Real', (br, k) => {
    const rf = X.tc(k, [hco, coDef('f', I)], 'RFn(f)'), Isub = X.tc(k, [hco, coDef('f', I)], `${I} sub dom(f)`);
    const allC = X.tc(k, [hco, coDef('f', I)], `all c. (c in ${I} -> ContIn(f, ${I}, c))`);
    const fOf = (cc, x, hxI) => mem(cc, `f[${x}]`, [rf, subE(cc, Isub, I, 'dom(f)', x, hxI)]);
    const toR = (cc, x, hxI) => X.tc(cc, [hxI, X.inst(X.defAx('cint'), ['a', 'b', x])], `${x} in Real`);
    const EPS = `all eps. (eps in Real -> 0 < eps -> ${UE('f', 'eps').replace(/\bA\b/g, I)})`;
    const eps = X.raa(k, EPS, (hn, c0) => [X.exE(X.notAllToEx(hn), 'e0', (he0, c1) => {
      const e0r = X.tc(c1, [he0], 'e0 in Real'), e0p = X.tc(c1, [he0], '0 < e0');
      const never = X.tc(c1, [he0], `all de. ~(de in Real & 0 < de & all x. all y. (x in ${I} -> y in ${I} -> abs(x - y) < de -> abs(f[x] - f[y]) < e0))`);
      const pre1 = X.gen(X.assume(c1, 'k in Nat', (hk, ck) => {
        const ip = use('IotaPos', ['k'], ck, [hk]);
        const kz = X.neSym(use('LtNe', ['0', 'iota(k)'], ck, [ip]));
        const d = 'iota(k)^-1';
        const na = X.tc(ck, [X.inst(never, [d]), mem(ck, d, [hk, kz]), use('InvPos', ['iota(k)'], ck, [hk, ip])], `~ all x. all y. (x in ${I} -> y in ${I} -> abs(x - y) < ${d} -> abs(f[x] - f[y]) < e0)`);
        return X.exE(X.notAllToEx(na), 'x', (hx, cx) => X.exE(X.notAllToEx(hx), 'y', (hy, cy) => {
          const xI = X.tc(cy, [hy], `x in ${I}`);
          const inner = X.exI(X.tc(cy, [hy], `y in ${I} & abs(x - y) < ${d} & ~ abs(f[x] - f[y]) < e0`), 'y', `y in ${I} & abs(x - y) < ${d} & ~ abs(f[x] - f[y]) < e0`, 'y');
          return X.exI(X.tc(cy, [toR(cy, 'x', xI), xI, inner], `x in Real & (${PS1})`), 'x', `x in Real & (${PS1})`, 'x');
        }, cx), ck);
      }), 'k');
      return X.exE(cc1(c1, [pre1]), 'p', (hp0, cp) => {
        const sp = X.tc(cp, [hp0], 'Seq(p)');
        const pp = X.tc(cp, [hp0], `all k. (k in Nat -> ${PS1.replace(/\bx\b/g, 'p[k]')})`);
        const hpI = X.gen(X.assume(cp, 'n in Nat', (hn, cn) => X.tc(cn, [X.inst(pp, ['n']), hn], `p[n] in ${I}`)), 'n');
        const pre2 = X.gen(X.assume(cp, 'k in Nat', (hk, ck) => {
          const ex = X.tc(ck, [X.inst(pp, ['k']), hk], `ex y. (y in ${I} & abs(p[k] - y) < iota(k)^-1 & ~ abs(f[p[k]] - f[y]) < e0)`);
          return X.exE(ex, 'y', (hy, cy) => X.exI(X.tc(cy, [toR(cy, 'y', X.tc(cy, [hy], `y in ${I}`)), hy], `y in Real & (${PS2.replace(/\bx\b/g, 'y')})`), 'x', `x in Real & (${PS2})`, 'y'), ck);
        }), 'k');
        return X.exE(cc2(cp, [pre2]), 'q', (hq0, cq) => {
          const sq = X.tc(cq, [hq0], 'Seq(q)');
          const pq = X.tc(cq, [hq0], `all k. (k in Nat -> ${PS2.replace(/\bx\b/g, 'q[k]')})`);
          const hqI = X.gen(X.assume(cq, 'n in Nat', (hn, cn) => X.tc(cn, [X.inst(pq, ['n']), hn], `q[n] in ${I}`)), 'n');
          return X.exE(use('BWin', ['p', 'a', 'b'], cq, [ar, br, sp, hpI]), 's', (hs0, cs0) => X.exE(hs0, 'c', (hs, cs) => {
            const si = X.tc(cs, [hs], 'SubIdx(s)'), cI = X.tc(cs, [hs], `c in ${I}`), convp = X.tc(cs, [hs], 'Conv(sseq(p,s), c)');
            const cr = toR(cs, 'c', cI);
            const P1 = imageConv(cs, rf, Isub, allC, 'p', sp, hpI, si, cI, convp);
            const ns = P1.ns;
            const ssq = use('SubSeqF', ['q', 's'], cs, [sq, ns]);
            const qval = (cn, n, hn) => X.tc(cn, [X.inst(X.tc(cn, [ssq], 'all k. (k in Nat -> sseq(q,s)[k] = q[s[k]])'), [n]), hn], `sseq(q,s)[${n}] = q[s[${n}]]`);
            // q∘s も c に収束
            const convq = convIntro(cs, 'sseq(q,s)', 'c', X.tc(cs, [ssq], 'Seq(sseq(q,s))'), cr, (c2, he, hpp) => {
              const e = 'eps * 2^-1';
              const er = mem(c2, e, [he]), ep = use('HalfPos', ['eps'], c2, [he, hpp]);
              return X.exE(use('ConvE', ['sseq(p,s)', 'c', e], c2, [convp, er, ep]), 'N1', (h1, d1) => X.exE(use('ArchInv', [e], d1, [er, ep]), 'K', (hK, d2) => {
                const n1 = X.tc(d2, [h1], 'N1 in Nat'), kn = X.tc(d2, [hK], 'K in Nat');
                const M = 'cup(N1, K)';
                return tailIntro(d2, M, use('NatCup', ['N1', 'K'], d2, [n1, kn]), n => `abs(sseq(q,s)[${n}] - c) < eps`, (cl, hn, hl) => {
                  const sn = use('NSeqVal', ['s', 'n'], cl, [ns, hn]);
                  const ps = X.tc(cl, [X.inst(pq, ['s[n]']), sn], 'q[s[n]] in cint(a,b) & abs(p[s[n]] - q[s[n]]) < iota(s[n])^-1 & ~ abs(f[p[s[n]]] - f[q[s[n]]]) < e0');
                  const qr = toR(cl, 'q[s[n]]', X.tc(cl, [ps], `q[s[n]] in ${I}`)), pr = mem(cl, 'p[s[n]]', [sp, sn]);
                  const g = [cr, he, qr, pr, sn, hn, kn];
                  const n1n = use('LeTrans', ['N1', M, 'n'], cl, [X.inst(X.thm('LeCupL'), ['N1', 'K']), hl]);
                  const kn2 = use('LeTrans', ['K', M, 'n'], cl, [X.inst(X.thm('LeCupR'), ['N1', 'K']), hl]);
                  const near = X.rw(P1.val(cl, 'n', hn), tailAt(cl, h1, 'N1', m => `abs(sseq(p,s)[${m}] - c) < ${e}`, 'n', hn, n1n), `abs(p[s[n]] - c) < ${e}`, cl);
                  const gen = X.tc(cl, [X.inst(use('IdxGe', ['s'], cl, [si]), ['n']), hn], 'n <= s[n]');
                  const ie = use('LeLtTrans', ['iota(s[n])^-1', 'iota(K)^-1', e], cl, [use('LeTrans', ['iota(s[n])^-1', 'iota(n)^-1', 'iota(K)^-1'], cl, [use('IotaInvMono', ['n', 's[n]'], cl, [hn, sn, gen]), use('IotaInvMono', ['K', 'n'], cl, [kn, hn, kn2])]), X.tc(cl, [hK], `iota(K)^-1 < ${e}`)]);
                  const qp = X.rw(use('AbsSubComm', ['p[s[n]]', 'q[s[n]]'], cl, g), use('LtTrans', ['abs(p[s[n]] - q[s[n]])', 'iota(s[n])^-1', e], cl, [X.tc(cl, [ps], 'abs(p[s[n]] - q[s[n]]) < iota(s[n])^-1'), ie]), `abs(q[s[n]] - p[s[n]]) < ${e}`, cl);
                  const r = X.rw(use('HalfSum', ['eps'], cl, g), use('ErrChain', ['q[s[n]]', 'p[s[n]]', 'c', e], cl, [...g, er, qp, near]), 'abs(q[s[n]] - c) < eps', cl);
                  return X.rw(X.sym(qval(cl, 'n', hn)), r, 'abs(sseq(q,s)[n] - c) < eps', cl);
                });
              }, d1));
            });
            const Q1 = imageConv(cs, rf, Isub, allC, 'q', sq, hqI, si, cI, convq);
            const e = 'e0 * 2^-1';
            const er = mem(cs, e, [e0r]), ep = use('HalfPos', ['e0'], cs, [e0r, e0p]);
            const fcr = fOf(cs, 'c', cI);
            return X.exE(use('Tail', ['compseq(f,sseq(p,s))', 'f[c]', 'compseq(f,sseq(q,s))', 'f[c]', e], cs, [P1.fc, Q1.fc, er, ep]), 'N', (hN, cN) => {
              const nN = X.tc(cN, [hN], 'N in Nat');
              const both = tailAt(cN, hN, 'N', n => `abs(compseq(f,sseq(p,s))[${n}] - f[c]) < ${e} & abs(compseq(f,sseq(q,s))[${n}] - f[c]) < ${e}`, 'N', nN, X.tc(cN, [X.refl('N')], 'N <= N'));
              const sN = use('NSeqVal', ['s', 'N'], cN, [ns, nN]);
              const ps = X.tc(cN, [X.inst(pq, ['s[N]']), sN], 'q[s[N]] in cint(a,b) & abs(p[s[N]] - q[s[N]]) < iota(s[N])^-1 & ~ abs(f[p[s[N]]] - f[q[s[N]]]) < e0');
              const fp = fOf(cN, 'p[s[N]]', X.tc(cN, [X.inst(hpI, ['s[N]']), sN], `p[s[N]] in ${I}`)), fq = fOf(cN, 'q[s[N]]', X.tc(cN, [ps], `q[s[N]] in ${I}`));
              const g = [fcr, fp, fq, er, e0r];
              const a1 = X.rw(use('AbsSubComm', ['f[p[s[N]]]', 'f[c]'], cN, g), X.rw(P1.fval(cN, 'N', nN), X.tc(cN, [both], `abs(compseq(f,sseq(p,s))[N] - f[c]) < ${e}`), `abs(f[p[s[N]]] - f[c]) < ${e}`, cN), `abs(f[c] - f[p[s[N]]]) < ${e}`, cN);
              const a2 = X.rw(use('AbsSubComm', ['f[q[s[N]]]', 'f[c]'], cN, g), X.rw(Q1.fval(cN, 'N', nN), X.tc(cN, [both], `abs(compseq(f,sseq(q,s))[N] - f[c]) < ${e}`), `abs(f[q[s[N]]] - f[c]) < ${e}`, cN), `abs(f[c] - f[q[s[N]]]) < ${e}`, cN);
              const r = X.rw(use('HalfSum', ['e0'], cN, g), use('ErrTwo', ['f[c]', 'f[p[s[N]]]', 'f[q[s[N]]]', e], cN, [...g, a1, a2]), 'abs(f[p[s[N]]] - f[q[s[N]]]) < e0', cN);
              return X.tc(cN, [r, ps], '0 < 0');
            }, cs);
          }, cs0), cq);
        }, cp);
      }, c1);
    }, c0), X.inst(X.thm('LtIrrefl'), ['0'])]);
    return X.tc(k, [ucDef('f', I), rf, Isub, eps], `UC(f, ${I})`);
  }))), ['f', 'a', 'b']));

module.exports = {};
