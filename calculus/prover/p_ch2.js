'use strict';
// テキスト第2章: 上限・下限, 実数の連続性, アルキメデスの公理
const K = require('./kit');
const { X, prove, intro, use, calc, mem } = K;
require('./p_abs');

// ---------- 空でない集合 ----------
prove('NonemptyEx', 'all X. (X != emptyset -> ex x. x in X)', '[B1]', () => X.gen(X.assume([], 'X != emptyset', (h, c) => {
  const e = X.assume(c, '~ ex x. x in X', (n, c2) => {
    const all = X.tc(c2, [n], 'all x. ~ x in X');
    const iff = X.tc(c2, [X.inst(all, ['z']), X.inst(X.defAx('empty'), ['z'])], 'z in X <-> z in emptyset');
    return use(X.axiom('Ext'), ['X', 'emptyset'], c2, [X.gen(iff, 'z')]);
  });
  return X.tc(c, [h, e], 'ex x. x in X');
}), 'X'));

prove('ExNonempty', 'all X. all x. (x in X -> X != emptyset)', '[B2]', () => X.genAll(X.assume([], 'x in X', (h, c) => {
  const e = X.assume(c, 'X = emptyset', (eq, c2) => X.rw(eq, h, 'x in emptyset', c2));
  return X.tc(c, [e, X.inst(X.defAx('empty'), ['x'])], 'X != emptyset');
}), ['X', 'x']));

// ---------- 上限の一意性 (定義 2.3 の sup を関数記号として導入するため) ----------
prove('SupUnique', 'all s. all t. all X. (IsSup(s,X) -> IsSup(t,X) -> s = t)', '[B3]', () => X.genAll(
  X.assume([], 'IsSup(s,X)', (h1, c1) => X.assume(c1, 'IsSup(t,X)', (h2, c) => {
    const d1 = X.inst(X.defAx('IsSup'), ['s', 'X']), d2 = X.inst(X.defAx('IsSup'), ['t', 'X']);
    const st = X.tc(c, [h1, h2, d1, d2, X.inst(X.tc(c, [h1, d1], 'all w. (UB(w,X) -> s <= w)'), ['t'])], 's <= t');
    const ts = X.tc(c, [h1, h2, d1, d2, X.inst(X.tc(c, [h2, d2], 'all w. (UB(w,X) -> t <= w)'), ['s'])], 't <= s');
    return use('LeAntisym', ['s', 't'], c, [st, ts]);
  })), ['s', 't', 'X']));

prove('InfUnique', 'all s. all t. all X. (IsInf(s,X) -> IsInf(t,X) -> s = t)', '[B4]', () => X.genAll(
  X.assume([], 'IsInf(s,X)', (h1, c1) => X.assume(c1, 'IsInf(t,X)', (h2, c) => {
    const d1 = X.inst(X.defAx('IsInf'), ['s', 'X']), d2 = X.inst(X.defAx('IsInf'), ['t', 'X']);
    const ts = X.tc(c, [h1, h2, d1, d2, X.inst(X.tc(c, [h1, d1], 'all w. (LB(w,X) -> w <= s)'), ['t'])], 't <= s');
    const st = X.tc(c, [h1, h2, d1, d2, X.inst(X.tc(c, [h2, d2], 'all w. (LB(w,X) -> w <= t)'), ['s'])], 's <= t');
    return use('LeAntisym', ['s', 't'], c, [st, ts]);
  })), ['s', 't', 'X']));

// ---------- 下限の存在 (テキスト公理 3.1(2)) ----------
// 補題: x ∈ X ⊆ ℝ なら x ∈ ℝ
prove('SubElem', 'all X. all Y. all x. (X sub Y -> x in X -> x in Y)', '[B5]', () => X.genAll(
  X.assume([], 'X sub Y', (h, c1) => X.assume(c1, 'x in X', (hx, c) =>
    X.tc(c, [h, hx, X.inst(X.tc(c, [h, X.inst(X.defAx('sub'), ['X', 'Y'])], 'all u. (u in X -> u in Y)'), ['x'])], 'x in Y'))), ['X', 'Y', 'x']));

prove('InfExists', 'all X. (X sub Real -> X != emptyset -> (ex b. LB(b,X)) -> ex s. IsInf(s,X))', '公理3.1(2)', () =>
  X.gen(X.assume([], 'X sub Real', (hs, c1) => X.assume(c1, 'X != emptyset', (hn, c2) => X.assume(c2, 'ex b. LB(b,X)', (hb, c) => {
    const Y = 'negset(X)';
    const dY = y => X.inst(X.defAx('negset'), ['X', y]);
    const inR = (cc, x, hx) => use('SubElem', ['X', 'Real', x], cc, [hs, hx]);
    // (1) Y ⊆ ℝ
    const ysub = X.tc(c, [X.gen(X.tc(c, [dY('u')], 'u in negset(X) -> u in Real'), 'u'), X.inst(X.defAx('sub'), [Y, 'Real'])], 'negset(X) sub Real');
    // (2) Y ≠ ∅
    const yne = X.exE(use('NonemptyEx', ['X'], c, [hn]), 'x', (hx, cx) => {
      const xr = inR(cx, 'x', hx);
      const nnx = X.rw(X.sym(use('NegNeg', ['x'], cx, [xr])), hx, '-(-x) in X', cx);
      const m = X.tc(cx, [dY('-x'), mem(cx, '-x', [xr]), nnx], '-x in negset(X)');
      return use('ExNonempty', [Y, '-x'], cx, [m]);
    });
    // (3) X の下界 b について -b は Y の上界
    const yub = X.exE(hb, 'b', (hb1, cb) => {
      const dlb = X.inst(X.defAx('LB'), ['b', 'X']);
      const br = X.tc(cb, [hb1, dlb], 'b in Real');
      const all = X.tc(cb, [hb1, dlb], 'all x. (x in X -> b <= x)');
      const yle = X.assume(cb, 'y in negset(X)', (hy, cy) => {
        const yr = X.tc(cy, [hy, dY('y')], 'y in Real');
        const ny = X.tc(cy, [hy, dY('y')], '-y in X');
        const ble = X.tc(cy, [X.inst(all, ['-y']), ny], 'b <= -y');
        const n = use('NegLe', ['b', '-y'], cy, [ble, yr, br]);
        return X.rw(use('NegNeg', ['y'], cy, [yr]), n, 'y <= -b', cy);
      });
      const ub = X.tc(cb, [X.inst(X.defAx('UB'), ['-b', Y]), mem(cb, '-b', [br]), X.gen(yle, 'y')], 'UB(-b, negset(X))');
      return X.exI(ub, 'b', 'UB(b, negset(X))', '-b');
    });
    // (4) R16
    const sup = use('R16', [Y], c, [ysub, X.neSym(X.neSym(yne)), yub]);
    // (5) Y の上限 s について -s は X の下限
    return X.exE(sup, 's', (hsup, cs) => {
      const dS = X.inst(X.defAx('IsSup'), ['s', Y]);
      const ubs = X.tc(cs, [hsup, dS], 'UB(s, negset(X))');
      const dU = X.inst(X.defAx('UB'), ['s', Y]);
      const sr = X.tc(cs, [ubs, dU], 's in Real');
      const allY = X.tc(cs, [ubs, dU], 'all y. (y in negset(X) -> y <= s)');
      const lbx = X.assume(cs, 'x in X', (hx, cx) => {
        const xr = inR(cx, 'x', hx);
        const nnx = X.rw(X.sym(use('NegNeg', ['x'], cx, [xr])), hx, '-(-x) in X', cx);
        const m = X.tc(cx, [dY('-x'), mem(cx, '-x', [xr]), nnx], '-x in negset(X)');
        const le = X.tc(cx, [X.inst(allY, ['-x']), m], '-x <= s');
        const n = use('NegLe', ['-x', 's'], cx, [le, sr, mem(cx, '-x', [xr])]);
        return X.rw(use('NegNeg', ['x'], cx, [xr]), n, '-s <= x', cx);
      });
      const lb = X.tc(cs, [X.inst(X.defAx('LB'), ['-s', 'X']), mem(cs, '-s', [sr]), X.gen(lbx, 'x')], 'LB(-s, X)');
      const great = X.assume(cs, 'LB(a, X)', (ha, ca) => {
        const dla = X.inst(X.defAx('LB'), ['a', 'X']);
        const ar = X.tc(ca, [ha, dla], 'a in Real');
        const alla = X.tc(ca, [ha, dla], 'all x. (x in X -> a <= x)');
        const yle = X.assume(ca, 'y in negset(X)', (hy, cy) => {
          const yr = X.tc(cy, [hy, dY('y')], 'y in Real');
          const ale = X.tc(cy, [X.inst(alla, ['-y']), X.tc(cy, [hy, dY('y')], '-y in X')], 'a <= -y');
          return X.rw(use('NegNeg', ['y'], cy, [yr]), use('NegLe', ['a', '-y'], cy, [ale, yr, ar]), 'y <= -a', cy);
        });
        const ub = X.tc(ca, [X.inst(X.defAx('UB'), ['-a', Y]), mem(ca, '-a', [ar]), X.gen(yle, 'y')], 'UB(-a, negset(X))');
        const sle = X.tc(ca, [X.inst(X.tc(ca, [hsup, dS], 'all w. (UB(w, negset(X)) -> s <= w)'), ['-a']), ub], 's <= -a');
        const n = use('NegLe', ['s', '-a'], ca, [sle, sr, mem(ca, '-a', [ar])]);
        return X.rw(use('NegNeg', ['a'], ca, [ar]), n, 'a <= -s', ca);
      });
      const inf = X.tc(cs, [X.inst(X.defAx('IsInf'), ['-s', 'X']), lb, X.gen(great, 'a')], 'IsInf(-s, X)');
      return X.exI(inf, 's', 'IsInf(s, X)', '-s');
    });
  }))), 'X'));

// ---------- アルキメデスの公理 (テキスト命題 3.2) ----------
prove('SubSubSelf', 'all x. all y. (x in Real -> y in Real -> x - (x - y) = y)', '[B6]', () => intro(['x', 'y'], [], c => calc(c, 'x - (x - y)', [
  ['x + -(x - y)', X.inst(X.defAx('minus'), ['x', 'x - y'])],
  ['x + (y - x)', use('SubNeg', ['y', 'x'], c)],
  ['(y - x) + x', use('R3', ['x', 'y - x'], c)],
  ['y', use('SubAdd', ['y', 'x'], c)],
])));
prove('LtSubAdd', 'all x. all a. all y. (x in Real -> a in Real -> y in Real -> x - a < y -> x < y + a)', '[B7]', () =>
  intro(['x', 'a', 'y'], ['x - a < y'], (c, [h]) => X.rw(use('SubAdd', ['x', 'a'], c), use('R14', ['x - a', 'y', 'a'], c, [h]), 'x < y + a', c)));
prove('IotaSMul', 'all m. all a. (m in Nat -> a in Real -> iota(S(m)) * a = iota(m) * a + a)', '[B8]', () =>
  X.genAll(X.assume([], 'm in Nat', (hm, c1) => X.assume(c1, 'a in Real', (ha, c) => calc(c, 'iota(S(m)) * a', [
    ['(iota(m) + 1) * a', use('IotaS', ['m'], c)],
    ['a * (iota(m) + 1)', use('R7', ['iota(m) + 1', 'a'], c)],
    ['a * iota(m) + a * 1', use('R10', ['a', 'iota(m)', '1'], c)],
    ['iota(m) * a + a * 1', use('R7', ['a', 'iota(m)'], c)],
    ['iota(m) * a + a', use('R8', ['a'], c)],
  ]))), ['m', 'a']));

prove('Archimedes', 'all a. all b. (a in Real -> b in Real -> 0 < a -> 0 < b -> ex n. (n in Nat & b < iota(n) * a))', '命題3.2', () =>
  intro(['a', 'b'], ['0 < a', '0 < b'], (c, [ha, hb]) => X.raa(c, 'ex n. (n in Nat & b < iota(n) * a)', (hng, c2) => {
    const Xa = 'ArchX(a)';
    const dX = y => X.inst(X.defAx('ArchX'), ['a', y]);
    // X ⊆ ℝ
    const xsub = X.tc(c2, [X.gen(X.tc(c2, [dX('u')], 'u in ArchX(a) -> u in Real'), 'u'), X.inst(X.defAx('sub'), [Xa, 'Real'])], 'ArchX(a) sub Real');
    // X ≠ ∅ (1·a ∈ X)
    const one = X.thm('NatOne');
    const w = X.exI(X.tc(c2, [one, X.refl('iota(onew) * a')], 'onew in Nat & iota(onew) * a = iota(onew) * a'), 'n', 'n in Nat & iota(onew) * a = iota(n) * a', 'onew');
    const m1 = X.tc(c2, [dX('iota(onew) * a'), mem(c2, 'iota(onew) * a', [one]), w], 'iota(onew) * a in ArchX(a)');
    const xne = use('ExNonempty', [Xa, 'iota(onew) * a'], c2, [m1]);
    // ¬G のもとで b は X の上界
    const notG = X.tc(c2, [hng], 'all n. ~ (n in Nat & b < iota(n) * a)');
    const yle = X.assume(c2, 'y in ArchX(a)', (hy, cy) => {
      const ex = X.tc(cy, [hy, dX('y')], 'ex n. (n in Nat & y = iota(n) * a)');
      return X.exE(ex, 'n', (hn, cn) => {
        const nn = X.tc(cn, [hn], 'n in Nat');
        const nlt = X.tc(cn, [X.inst(notG, ['n']), nn], '~ b < iota(n) * a');
        const le = use('NotLtLe', ['b', 'iota(n) * a'], cn, [nlt, nn]);
        return X.rw(X.sym(X.tc(cn, [hn], 'y = iota(n) * a')), le, 'y <= b', cn);
      });
    });
    const ub = X.tc(c2, [X.inst(X.defAx('UB'), ['b', Xa]), X.gen(yle, 'y')], 'UB(b, ArchX(a))');
    const sup = use('R16', [Xa], c2, [xsub, xne, X.exI(ub, 'b', 'UB(b, ArchX(a))', 'b')]);
    const bad = X.exE(sup, 's', (hs, cs) => {
      const dS = X.inst(X.defAx('IsSup'), ['s', Xa]);
      const ubs = X.tc(cs, [hs, dS], 'UB(s, ArchX(a))');
      const dU = X.inst(X.defAx('UB'), ['s', Xa]);
      const sr = X.tc(cs, [ubs, dU], 's in Real');
      const f = [sr];
      // s - a < s
      const sl = use('PosSub', ['s - a', 's'], cs, [X.rw(X.sym(use('SubSubSelf', ['s', 'a'], cs, f)), ha, '0 < s - (s - a)', cs), ...f]);
      // s - a は上界でない
      const notub = X.tc(cs, [X.assume(cs, 'UB(s - a, ArchX(a))', (hu, cu) => {
        const sle = X.tc(cu, [X.inst(X.tc(cu, [hs, dS], 'all w. (UB(w, ArchX(a)) -> s <= w)'), ['s - a']), hu], 's <= s - a');
        return X.tc(cu, [sle, use('LeNotLt', ['s', 's - a'], cu), sl], '~ UB(s - a, ArchX(a))');
      })], '~ UB(s - a, ArchX(a))');
      const nall = X.tc(cs, [notub, X.inst(X.defAx('UB'), ['s - a', Xa]), mem(cs, 's - a', f)], '~ all x. (x in ArchX(a) -> x <= s - a)');
      return X.exE(X.notAllToEx(nall), 'y', (hy, cy) => {
        const yX = X.tc(cy, [hy], 'y in ArchX(a)');
        const yr = X.tc(cy, [yX, dX('y')], 'y in Real');
        const lt = use('NotLeLt', ['s - a', 'y'], cy, [X.tc(cy, [hy], '~ y <= s - a'), yr, ...f]);
        return X.exE(X.tc(cy, [yX, dX('y')], 'ex n. (n in Nat & y = iota(n) * a)'), 'm', (hm, cm) => {
          const mn = X.tc(cm, [hm], 'm in Nat');
          const ym = X.tc(cm, [hm], 'y = iota(m) * a');
          const s1 = use('LtSubAdd', ['s', 'a', 'y'], cm, [lt, yr, ...f]);                     // s < y + a
          const s2 = X.rw(ym, s1, 's < iota(m) * a + a', cm);
          const s3 = X.rw(X.sym(use('IotaSMul', ['m', 'a'], cm, [mn])), s2, 's < iota(S(m)) * a', cm);
          const sm = use('NatS', ['m'], cm, [mn]);
          const wit = X.exI(X.tc(cm, [sm, X.refl('iota(S(m)) * a')], 'S(m) in Nat & iota(S(m)) * a = iota(S(m)) * a'), 'n', 'n in Nat & iota(S(m)) * a = iota(n) * a', 'S(m)');
          const inX = X.tc(cm, [dX('iota(S(m)) * a'), mem(cm, 'iota(S(m)) * a', [sm]), wit], 'iota(S(m)) * a in ArchX(a)');
          const all = X.tc(cm, [ubs, dU], 'all x. (x in ArchX(a) -> x <= s)');
          const le = X.tc(cm, [X.inst(all, ['iota(S(m)) * a']), inX], 'iota(S(m)) * a <= s');
          const ss = use('LtLeTrans', ['s', 'iota(S(m)) * a', 's'], cm, [s3, le]);
          return X.tc(cm, [ss, X.inst(X.thm('LtIrrefl'), ['s'])], '0 < 0');
        });
      });
    });
    return [bad, X.inst(X.thm('LtIrrefl'), ['0'])];
  })));

module.exports = {};
