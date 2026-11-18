'use strict';
// テキスト第3章 5節・6節: 単調収束定理, 区間縮小法, Bolzano–Weierstrass, Cauchy 列
const K = require('./kit');
const { X, C, prove, intro, use, calc, mem, P } = K;
const { def, fthm } = require('./theory');
const { indNat, monoThm } = require('./p_nat');
const { convIntro, tailIntro, tailAt } = require('./p_seq');
require('./p_seq2');

fthm('RanSeq', 'all a. (Seq(a) -> ran(a) sub Real & all y. (y in ran(a) <-> ex j. (j in Nat & y = a[j])))', '[S16]', '値域の定義');
// 部分列の抽出 (ω の整列性と再帰定理による. 図式 [CC] のインスタンス)
fthm('ExtractSub', 'all a. all c. (Seq(a) -> (all k. (k in Nat -> all N. (N in Nat -> ex n. (n in Nat & N <= n & abs(a[n] - c) < iota(k)^-1)))) -> ex s. (SubIdx(s) & all k. (k in Nat -> abs(a[s[k]] - c) < iota(k)^-1)))', '[S28]', '定理(部分列の抽出)');

// ---------------- 単調列の比較 ----------------
monoThm('MonoIncLe', '[C20]', ['a'], ['MonoInc(a)'], t => `a[${t}]`, (c, [h], hn) =>
  X.tc(c, [X.inst(X.tc(c, [h, X.inst(X.defAx('MonoInc'), ['a'])], 'all n. (n in Nat -> a[n] <= a[S(n)])'), ['n']), hn], 'a[n] <= a[S(n)]'));
monoThm('MonoDecLe', '[C21]', ['a'], ['MonoDec(a)'], t => `a[${t}]`, (c, [h], hn) =>
  X.tc(c, [X.inst(X.tc(c, [h, X.inst(X.defAx('MonoDec'), ['a'])], 'all n. (n in Nat -> a[S(n)] <= a[n])'), ['n']), hn], 'a[S(n)] <= a[n]'), 'ge');

// x - e < y → -e < y - x,   y < x + e → y - x < e
prove('SubLtSwap', 'all x. all e. all y. (x in Real -> e in Real -> y in Real -> x - e < y -> -e < y - x)', '[E31]', () => intro(['x', 'e', 'y'], ['x - e < y'], (c, [h]) => {
  const l = use('R14', ['x - e', 'y', '-x'], c, [h]);
  const e1 = calc(c, '(x - e) + -x', [['(x + -e) + -x', X.inst(X.defAx('minus'), ['x', 'e'])], ['(-e + x) + -x', use('R3', ['x', '-e'], c)], ['-e + (x + -x)', use('R2', ['-e', 'x', '-x'], c)], ['-e + 0', use('R5', ['x'], c)], ['-e', use('R4', ['-e'], c)]]);
  return X.rw(X.sym(X.inst(X.defAx('minus'), ['y', 'x'])), X.rw(e1, l, '-e < y + -x', c), '-e < y - x', c);
}));
prove('LtAddSwap', 'all x. all e. all y. (x in Real -> e in Real -> y in Real -> y < x + e -> y - x < e)', '[E32]', () => intro(['x', 'e', 'y'], ['y < x + e'], (c, [h]) => {
  const l = use('R14', ['y', 'x + e', '-x'], c, [h]);
  const e1 = calc(c, '(x + e) + -x', [['(e + x) + -x', use('R3', ['x', 'e'], c)], ['e + (x + -x)', use('R2', ['e', 'x', '-x'], c)], ['e + 0', use('R5', ['x'], c)], ['e', use('R4', ['e'], c)]]);
  return X.rw(X.sym(X.inst(X.defAx('minus'), ['y', 'x'])), X.rw(e1, l, 'y + -x < e', c), 'y - x < e', c);
}));
// x - e < y < x + e → |y - x| < e
prove('BandAbs', 'all x. all e. all y. (x in Real -> e in Real -> y in Real -> x - e < y -> y < x + e -> abs(y - x) < e)', '[E33]', () => intro(['x', 'e', 'y'], ['x - e < y', 'y < x + e'], (c, [h1, h2]) =>
  use('LtAbs', ['y - x', 'e'], c, [use('SubLtSwap', ['x', 'e', 'y'], c, [h1]), use('LtAddSwap', ['x', 'e', 'y'], c, [h2])])));
prove('SubLtSelf', 'all x. all e. (x in Real -> e in Real -> 0 < e -> x - e < x)', '[E34]', () => intro(['x', 'e'], ['0 < e'], (c, [h]) => {
  const l = use('LtAddPos', ['x - e', 'e'], c, [h]);
  return X.rw(use('SubAdd', ['x', 'e'], c), l, 'x - e < x', c);
}));

// 上限の性質
const supDef = (s, E) => X.inst(X.defAx('IsSup'), [s, E]);
const ubDef = (b, E) => X.inst(X.defAx('UB'), [b, E]);
/// E ⊆ ℝ, IsSup(s,E), 0<e → ∃x (x∈E ∧ s - e < x)
prove('SupApprox', 'all s. all E. all e. (E sub Real -> IsSup(s,E) -> e in Real -> 0 < e -> ex x. (x in E & s - e < x))', '[C22]', () => X.genAll(
  X.assume([], 'E sub Real', (hE, k0) => X.assume(k0, 'IsSup(s,E)', (hs, k1) => X.assume(k1, 'e in Real', (he, k2) => X.assume(k2, '0 < e', (hp, k) => {
    const sr = X.tc(k, [hs, supDef('s', 'E'), ubDef('s', 'E')], 's in Real');
    const least = X.tc(k, [hs, supDef('s', 'E')], 'all w. (UB(w,E) -> s <= w)');
    const notub = X.raa(k, '~ UB(s - e, E)', (hn, c2) => {
      const le = X.tc(c2, [X.inst(least, ['s - e']), hn], 's <= s - e');
      return [use('SubLtSelf', ['s', 'e'], c2, [sr, he, hp]), use('LeNotLt', ['s', 's - e'], c2, [le])];
    });
    const nall = X.tc(k, [notub, ubDef('s - e', 'E'), mem(k, 's - e', [sr, he])], '~ all x. (x in E -> x <= s - e)');
    return X.exE(X.notAllToEx(nall), 'x', (hx, cx) => {
      const xe = X.tc(cx, [hx], 'x in E');
      const xr = use('SubElem', ['E', 'Real', 'x'], cx, [hE, xe]);
      const lt = use('NotLeLt', ['s - e', 'x'], cx, [mem(cx, 's - e', [sr, he]), xr, X.tc(cx, [hx], '~ x <= s - e')]);
      return X.exI(X.tc(cx, [xe, lt], 'x in E & s - e < x'), 'x', 'x in E & s - e < x', 'x');
    }, k);
  })))), ['s', 'E', 'e']));
// 下限についても同様: x < s + e
prove('InfApprox', 'all s. all E. all e. (E sub Real -> IsInf(s,E) -> e in Real -> 0 < e -> ex x. (x in E & x < s + e))', '[C23]', () => X.genAll(
  X.assume([], 'E sub Real', (hE, k0) => X.assume(k0, 'IsInf(s,E)', (hs, k1) => X.assume(k1, 'e in Real', (he, k2) => X.assume(k2, '0 < e', (hp, k) => {
    const lbDef = (b) => X.inst(X.defAx('LB'), [b, 'E']);
    const sr = X.tc(k, [hs, X.inst(X.defAx('IsInf'), ['s', 'E']), lbDef('s')], 's in Real');
    const most = X.tc(k, [hs, X.inst(X.defAx('IsInf'), ['s', 'E'])], 'all w. (LB(w,E) -> w <= s)');
    const notlb = X.raa(k, '~ LB(s + e, E)', (hn, c2) => {
      const le = X.tc(c2, [X.inst(most, ['s + e']), hn], 's + e <= s');
      return [use('LtAddPos', ['s', 'e'], c2, [sr, he, hp]), use('LeNotLt', ['s + e', 's'], c2, [le])];
    });
    const nall = X.tc(k, [notlb, lbDef('s + e'), mem(k, 's + e', [sr, he])], '~ all x. (x in E -> s + e <= x)');
    return X.exE(X.notAllToEx(nall), 'x', (hx, cx) => {
      const xe = X.tc(cx, [hx], 'x in E');
      const xr = use('SubElem', ['E', 'Real', 'x'], cx, [hE, xe]);
      const lt = use('NotLeLt', ['x', 's + e'], cx, [mem(cx, 's + e', [sr, he]), xr, X.tc(cx, [hx], '~ s + e <= x')]);
      return X.exI(X.tc(cx, [xe, lt], 'x in E & x < s + e'), 'x', 'x in E & x < s + e', 'x');
    }, k);
  })))), ['s', 'E', 'e']));

// ---------------- 定理 5.3: 有界な単調数列の収束 ----------------
const ranOf = (c, sa) => use('RanSeq', ['a'], c, [sa]);
const ranMem = (c, ran, n, hn, sa) => { // c ⊢ a[n] ∈ ran(a)
  const iff = X.inst(X.tc(c, [ran], 'all y. (y in ran(a) <-> ex j. (j in Nat & y = a[j]))'), [`a[${n}]`]);
  const w = X.exI(X.tc(c, [hn, X.refl(`a[${n}]`)], `${n} in Nat & a[${n}] = a[${n}]`), 'j', `j in Nat & a[${n}] = a[j]`, n);
  return X.tc(c, [iff, w], `a[${n}] in ran(a)`);
};
const ranElim = (c, ran, y, hy, body, ev = 'n') => { // y ∈ ran(a) から ev をとる
  const iff = X.inst(X.tc(c, [ran], 'all y. (y in ran(a) <-> ex j. (j in Nat & y = a[j]))'), [y]);
  return X.exE(X.tc(c, [iff, hy], `ex j. (j in Nat & ${y} = a[j])`), ev, body, c);
};
prove('MonoConv', 'all a. all M. (MonoInc(a) -> M in Real -> (all n. (n in Nat -> a[n] <= M)) -> ex al. Conv(a,al))', '定理5.3(1)', () => X.genAll(
  X.assume([], 'MonoInc(a)', (hm, k1) => X.assume(k1, 'M in Real', (hM, k2) => X.assume(k2, 'all n. (n in Nat -> a[n] <= M)', (hb, k) => {
    const sa = X.tc(k, [hm, X.inst(X.defAx('MonoInc'), ['a'])], 'Seq(a)');
    const ran = ranOf(k, sa);
    const rs = X.tc(k, [ran], 'ran(a) sub Real');
    const one = X.thm('NatOne');
    const ne = use('ExNonempty', ['ran(a)', 'a[onew]'], k, [ranMem(k, ran, 'onew', one, sa)]);
    const ub = X.tc(k, [ubDef('M', 'ran(a)'), hM, X.gen(X.assume(k, 'y in ran(a)', (hy, cy) => ranElim(cy, ran, 'y', hy, (hn, cn) => {
      const nn = X.tc(cn, [hn], 'n in Nat');
      return X.rw(X.sym(X.tc(cn, [hn], 'y = a[n]')), X.tc(cn, [X.inst(hb, ['n']), nn], 'a[n] <= M'), 'y <= M', cn);
    })), 'y')], 'UB(M, ran(a))');
    const ex = use('R16', ['ran(a)'], k, [rs, ne, X.exI(ub, 'b', 'UB(b, ran(a))', 'M')]);
    return X.exE(ex, 's', (hs, cs) => {
      const sr = X.tc(cs, [hs, supDef('s', 'ran(a)'), ubDef('s', 'ran(a)')], 's in Real');
      const ubs = X.tc(cs, [hs, supDef('s', 'ran(a)'), ubDef('s', 'ran(a)')], 'all x. (x in ran(a) -> x <= s)');
      const conv = convIntro(cs, 'a', 's', sa, sr, (c2, he, hp) => X.exE(use('SupApprox', ['s', 'ran(a)', 'eps'], c2, [rs, hs, he, hp]), 'x', (hx, cx) =>
        ranElim(cx, ran, 'x', X.tc(cx, [hx], 'x in ran(a)'), (hN0, cN0) => {
          const nN = X.tc(cN0, [hN0], 'i0 in Nat');
          const lowN = X.rw(X.tc(cN0, [hN0], 'x = a[i0]'), X.tc(cN0, [hx], 's - eps < x'), 's - eps < a[i0]', cN0);
          const ex2 = X.exI(X.tc(cN0, [nN, lowN], 'i0 in Nat & s - eps < a[i0]'), 'N', 'N in Nat & s - eps < a[N]', 'i0');
          return X.exE(ex2, 'N', (hN, cN) => tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), m => `abs(a[${m}] - s) < eps`, (cl, hn, hl) => {
            const f = [sa, hn, sr, he];
            const mono = use('MonoIncLe', ['a', 'N', 'n'], cl, [hm, X.tc(cl, [hN], 'N in Nat'), hn, hl]);
            const lo = use('LtLeTrans', ['s - eps', 'a[N]', 'a[n]'], cl, [X.tc(cl, [hN], 's - eps < a[N]'), mono]);
            const up = X.tc(cl, [X.inst(ubs, ['a[n]']), ranMem(cl, ran, 'n', hn, sa)], 'a[n] <= s');
            const up2 = use('LeLtTrans', ['a[n]', 's', 's + eps'], cl, [up, use('LtAddPos', ['s', 'eps'], cl, [...f, hp])]);
            return use('BandAbs', ['s', 'eps', 'a[n]'], cl, [...f, lo, up2]);
          }), cN0);
        }, 'i0')));
      return X.exI(conv, 'al', 'Conv(a,al)', 's');
    }, k);
  }))), ['a', 'M']));
prove('MonoConvDec', 'all a. all M. (MonoDec(a) -> M in Real -> (all n. (n in Nat -> M <= a[n])) -> ex al. Conv(a,al))', '定理5.3(2)', () => X.genAll(
  X.assume([], 'MonoDec(a)', (hm, k1) => X.assume(k1, 'M in Real', (hM, k2) => X.assume(k2, 'all n. (n in Nat -> M <= a[n])', (hb, k) => {
    const sa = X.tc(k, [hm, X.inst(X.defAx('MonoDec'), ['a'])], 'Seq(a)');
    const ran = ranOf(k, sa);
    const rs = X.tc(k, [ran], 'ran(a) sub Real');
    const one = X.thm('NatOne');
    const ne = use('ExNonempty', ['ran(a)', 'a[onew]'], k, [ranMem(k, ran, 'onew', one, sa)]);
    const lbDef = (b, E) => X.inst(X.defAx('LB'), [b, E]);
    const lb = X.tc(k, [lbDef('M', 'ran(a)'), hM, X.gen(X.assume(k, 'y in ran(a)', (hy, cy) => ranElim(cy, ran, 'y', hy, (hn, cn) => {
      const nn = X.tc(cn, [hn], 'n in Nat');
      return X.rw(X.sym(X.tc(cn, [hn], 'y = a[n]')), X.tc(cn, [X.inst(hb, ['n']), nn], 'M <= a[n]'), 'M <= y', cn);
    })), 'y')], 'LB(M, ran(a))');
    const ex = use('InfExists', ['ran(a)'], k, [rs, ne, X.exI(lb, 'b', 'LB(b, ran(a))', 'M')]);
    return X.exE(ex, 's', (hs, cs) => {
      const infD = X.inst(X.defAx('IsInf'), ['s', 'ran(a)']);
      const sr = X.tc(cs, [hs, infD, lbDef('s', 'ran(a)')], 's in Real');
      const lbs = X.tc(cs, [hs, infD, lbDef('s', 'ran(a)')], 'all x. (x in ran(a) -> s <= x)');
      const conv = convIntro(cs, 'a', 's', sa, sr, (c2, he, hp) => X.exE(use('InfApprox', ['s', 'ran(a)', 'eps'], c2, [rs, hs, he, hp]), 'x', (hx, cx) =>
        ranElim(cx, ran, 'x', X.tc(cx, [hx], 'x in ran(a)'), (hN0, cN0) => {
          const nN = X.tc(cN0, [hN0], 'i0 in Nat');
          const upN = X.rw(X.tc(cN0, [hN0], 'x = a[i0]'), X.tc(cN0, [hx], 'x < s + eps'), 'a[i0] < s + eps', cN0);
          const ex2 = X.exI(X.tc(cN0, [nN, upN], 'i0 in Nat & a[i0] < s + eps'), 'N', 'N in Nat & a[N] < s + eps', 'i0');
          return X.exE(ex2, 'N', (hN, cN) => tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), m => `abs(a[${m}] - s) < eps`, (cl, hn, hl) => {
            const f = [sa, hn, sr, he];
            const mono = use('MonoDecLe', ['a', 'N', 'n'], cl, [hm, X.tc(cl, [hN], 'N in Nat'), hn, hl]);
            const up = use('LeLtTrans', ['a[n]', 'a[N]', 's + eps'], cl, [mono, X.tc(cl, [hN], 'a[N] < s + eps')]);
            const lo = X.tc(cl, [X.inst(lbs, ['a[n]']), ranMem(cl, ran, 'n', hn, sa)], 's <= a[n]');
            const lo2 = use('LtLeTrans', ['s - eps', 's', 'a[n]'], cl, [use('SubLtSelf', ['s', 'eps'], cl, [...f, hp]), lo]);
            return use('BandAbs', ['s', 'eps', 'a[n]'], cl, [...f, lo2, up]);
          }), cN0);
        }, 'i0')));
      return X.exI(conv, 'al', 'Conv(a,al)', 's');
    }, k);
  }))), ['a', 'M']));

// ---------------- 定理 5.10: 区間縮小法 ----------------
prove('NestedInt', 'all a. all b. (MonoInc(a) -> MonoDec(b) -> (all n. (n in Nat -> a[n] <= b[n])) -> ex x. (x in Real & all n. (n in Nat -> a[n] <= x & x <= b[n])))', '定理5.10', () => X.genAll(
  X.assume([], 'MonoInc(a)', (ha, k1) => X.assume(k1, 'MonoDec(b)', (hb, k2) => X.assume(k2, 'all n. (n in Nat -> a[n] <= b[n])', (hab, k) => {
    const sa = X.tc(k, [ha, X.inst(X.defAx('MonoInc'), ['a'])], 'Seq(a)'), sb = X.tc(k, [hb, X.inst(X.defAx('MonoDec'), ['b'])], 'Seq(b)');
    const ran = ranOf(k, sa);
    const rs = X.tc(k, [ran], 'ran(a) sub Real');
    const one = X.thm('NatOne');
    const ne = use('ExNonempty', ['ran(a)', 'a[onew]'], k, [ranMem(k, ran, 'onew', one, sa)]);
    const ubm = X.gen(X.assume(k, 'm in Nat', (hm, cm) => X.tc(cm, [ubDef('b[m]', 'ran(a)'), mem(cm, 'b[m]', [sb, hm]), X.gen(X.assume(cm, 'y in ran(a)', (hy, cy) => ranElim(cy, ran, 'y', hy, (hn, cn) => {
      const nn = X.tc(cn, [hn], 'n in Nat');
      const tot = use('OmegaTotal', ['n', 'm'], cn, [use('NatOmega', ['n'], cn, [nn]), use('NatOmega', ['m'], cn, [hm])]);
      const c1 = X.assume(cn, 'n <= m', (h1, c3) => use('LeTrans', ['a[n]', 'a[m]', 'b[m]'], c3, [use('MonoIncLe', ['a', 'n', 'm'], c3, [ha, nn, hm, h1]), X.tc(c3, [X.inst(hab, ['m']), hm], 'a[m] <= b[m]')]));
      const c2 = X.assume(cn, 'm < n', (h1, c3) => use('LeTrans', ['a[n]', 'b[n]', 'b[m]'], c3, [X.tc(c3, [X.inst(hab, ['n']), nn], 'a[n] <= b[n]'), use('MonoDecLe', ['b', 'm', 'n'], c3, [hb, hm, nn, X.tc(c3, [h1], 'm <= n')])]));
      const le = X.tc(cn, [tot, c1, c2], 'a[n] <= b[m]');
      return X.rw(X.sym(X.tc(cn, [hn], 'y = a[n]')), le, 'y <= b[m]', cn);
    })), 'y')], 'UB(b[m], ran(a))')), 'm');
    const ub1 = X.tc(k, [X.inst(ubm, ['onew']), one], 'UB(b[onew], ran(a))');
    const ex = use('R16', ['ran(a)'], k, [rs, ne, X.exI(ub1, 'b', 'UB(b, ran(a))', 'b[onew]')]);
    return X.exE(ex, 'x', (hx, cx) => {
      const xr = X.tc(cx, [hx, supDef('x', 'ran(a)'), ubDef('x', 'ran(a)')], 'x in Real');
      const ubx = X.tc(cx, [hx, supDef('x', 'ran(a)'), ubDef('x', 'ran(a)')], 'all y. (y in ran(a) -> y <= x)');
      const least = X.tc(cx, [hx, supDef('x', 'ran(a)')], 'all w. (UB(w, ran(a)) -> x <= w)');
      const all = X.gen(X.assume(cx, 'n in Nat', (hn, cn) => X.tc(cn, [X.inst(ubx, ['a[n]']), ranMem(cn, ran, 'n', hn, sa), X.inst(least, ['b[n]']), X.inst(ubm, ['n']), hn], 'a[n] <= x & x <= b[n]')), 'n');
      return X.exI(X.tc(cx, [xr, all], 'x in Real & all n. (n in Nat -> a[n] <= x & x <= b[n])'), 'x', 'x in Real & all n. (n in Nat -> a[n] <= x & x <= b[n])', 'x');
    }, k);
  }))), ['a', 'b']));

module.exports = {};
