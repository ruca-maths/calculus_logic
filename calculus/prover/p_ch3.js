'use strict';
// テキスト第3章: 数列の極限
const K = require('./kit');
const { X, prove, intro, use, calc, mem } = K;
require('./p_ch2');

const convDef = (a, al) => X.inst(X.defAx('Conv'), [a, al]);
const QF = (a, al, e) => `ex N. (N in Nat & all n. (n in Nat -> N <= n -> abs(${a}[n] - ${al}) < ${e}))`;

// ---------- 収束の定義の展開 ----------
prove('ConvSeq', 'all a. all al. (Conv(a,al) -> Seq(a))', '[C1]', () => X.genAll(X.assume([], 'Conv(a,al)', (h, c) => X.tc(c, [h, convDef('a', 'al')], 'Seq(a)')), ['a', 'al']));
prove('ConvR', 'all a. all al. (Conv(a,al) -> al in Real)', '[C2]', () => X.genAll(X.assume([], 'Conv(a,al)', (h, c) => X.tc(c, [h, convDef('a', 'al')], 'al in Real')), ['a', 'al']));
prove('ConvE', `all a. all al. all eps. (Conv(a,al) -> eps in Real -> 0 < eps -> ${QF('a', 'al', 'eps')})`, '[C3]', () => X.genAll(
  X.assume([], 'Conv(a,al)', (h, c1) => X.assume(c1, 'eps in Real', (he, c2) => X.assume(c2, '0 < eps', (hp, c) => {
    const all = X.tc(c, [h, convDef('a', 'al')], `all eps. (eps in Real -> 0 < eps -> ${QF('a', 'al', 'eps')})`);
    return X.tc(c, [X.inst(all, ['eps']), he, hp], QF('a', 'al', 'eps'));
  }))), ['a', 'al', 'eps']));

// ---------- ω の順序 (一般の集合で成り立つ) ----------
prove('SubCupL', 'all m. all n. m sub cup(m,n)', '[C4]', () => X.genAll(X.tc([], [
  X.gen(X.tc([], [X.inst(X.defAx('cup'), ['m', 'n', 'u'])], 'u in m -> u in cup(m,n)'), 'u'), X.inst(X.defAx('sub'), ['m', 'cup(m,n)'])], 'm sub cup(m,n)'), ['m', 'n']));
prove('SubCupR', 'all m. all n. n sub cup(m,n)', '[C5]', () => X.genAll(X.tc([], [
  X.gen(X.tc([], [X.inst(X.defAx('cup'), ['m', 'n', 'u'])], 'u in n -> u in cup(m,n)'), 'u'), X.inst(X.defAx('sub'), ['n', 'cup(m,n)'])], 'n sub cup(m,n)'), ['m', 'n']));
prove('SubLe', 'all x. all y. (x sub y -> x <= y)', '[C6]', () => X.genAll(X.assume([], 'x sub y', (h, c) => X.tc(c, [h, X.inst(X.defAx('lt'), ['x', 'y'])], 'x <= y')), ['x', 'y']));
prove('LeCupL', 'all m. all n. m <= cup(m,n)', '[C7]', () => X.genAll(use('SubLe', ['m', 'cup(m,n)'], [], [X.inst(X.thm('SubCupL'), ['m', 'n'])]), ['m', 'n']));
prove('LeCupR', 'all m. all n. n <= cup(m,n)', '[C8]', () => X.genAll(use('SubLe', ['n', 'cup(m,n)'], [], [X.inst(X.thm('SubCupR'), ['m', 'n'])]), ['m', 'n']));

// ---------- 尾部の共通化 ----------
const TAIL = 'ex N. (N in Nat & all n. (n in Nat -> N <= n -> abs(a[n] - al) < eps & abs(b[n] - be) < eps))';
prove('Tail', `all a. all al. all b. all be. all eps. (Conv(a,al) -> Conv(b,be) -> eps in Real -> 0 < eps -> ${TAIL})`, '[C9]', () => X.genAll(
  X.assume([], 'Conv(a,al)', (ha, c1) => X.assume(c1, 'Conv(b,be)', (hb, c2) => X.assume(c2, 'eps in Real', (he, c3) => X.assume(c3, '0 < eps', (hp, c) => {
    const ea = use('ConvE', ['a', 'al', 'eps'], c, [ha, he, hp]);
    const eb = use('ConvE', ['b', 'be', 'eps'], c, [hb, he, hp]);
    return X.exE(ea, 'N1', (q1, d1) => X.exE(eb, 'N2', (q2, d) => {
      const M = 'cup(N1,N2)';
      const n1 = X.tc(d, [q1], 'N1 in Nat'), n2 = X.tc(d, [q2], 'N2 in Nat');
      const mN = use('NatCup', ['N1', 'N2'], d, [n1, n2]);
      const body = X.assume(d, 'n in Nat', (hn, dn) => X.assume(dn, `${M} <= n`, (hm, dm) => {
        const l1 = use('LeTrans', ['N1', M, 'n'], dm, [X.inst(X.thm('LeCupL'), ['N1', 'N2']), hm]);
        const l2 = use('LeTrans', ['N2', M, 'n'], dm, [X.inst(X.thm('LeCupR'), ['N1', 'N2']), hm]);
        const a1 = X.tc(dm, [X.inst(X.tc(dm, [q1], 'all n. (n in Nat -> N1 <= n -> abs(a[n] - al) < eps)'), ['n']), hn, l1], 'abs(a[n] - al) < eps');
        const b1 = X.tc(dm, [X.inst(X.tc(dm, [q2], 'all n. (n in Nat -> N2 <= n -> abs(b[n] - be) < eps)'), ['n']), hn, l2], 'abs(b[n] - be) < eps');
        return X.tc(dm, [a1, b1], 'abs(a[n] - al) < eps & abs(b[n] - be) < eps');
      }));
      const w = X.tc(d, [mN, X.gen(body, 'n')], `${M} in Nat & all n. (n in Nat -> ${M} <= n -> abs(a[n] - al) < eps & abs(b[n] - be) < eps)`);
      return X.exI(w, 'N', 'N in Nat & all n. (n in Nat -> N <= n -> abs(a[n] - al) < eps & abs(b[n] - be) < eps)', M);
    }, d1));
  })))), ['a', 'al', 'b', 'be', 'eps']));

// ---------- 命題 1.1 ----------
prove('EpsEq', 'all a. all b. (a in Real -> b in Real -> (all eps. (eps in Real -> 0 < eps -> abs(a - b) < eps)) -> a = b)', '命題1.1', () =>
  intro(['a', 'b'], ['all eps. (eps in Real -> 0 < eps -> abs(a - b) < eps)'], (c, [h]) => X.raa(c, 'a = b', (hn, c2) => {
    const ne = use('SubNeZero', ['a', 'b'], c2, [hn]);
    const p = use('AbsPos', ['a - b'], c2, [ne]);
    const l = X.tc(c2, [X.inst(h, ['abs(a - b)']), mem(c2, 'abs(a - b)'), p], 'abs(a - b) < abs(a - b)');
    return [l, X.inst(X.thm('LtIrrefl'), ['abs(a - b)'])];
  })));

// ---------- 極限の一意性 (テキスト命題 1.3) ----------
prove('ErrTwo', 'all x. all al. all be. all eps. (x in Real -> al in Real -> be in Real -> eps in Real -> abs(x - al) < eps -> abs(x - be) < eps -> abs(al - be) < eps + eps)', '[C10]', () =>
  intro(['x', 'al', 'be', 'eps'], ['abs(x - al) < eps', 'abs(x - be) < eps'], (c, [h1, h2]) => {
    const s = use('SubSplit', ['al', 'be', 'x'], c);
    const t = X.rw(X.sym(s), use('Triangle', ['al - x', 'x - be'], c), 'abs(al - be) <= abs(al - x) + abs(x - be)', c);
    const h1b = X.rw(use('AbsSubComm', ['x', 'al'], c), h1, 'abs(al - x) < eps', c);
    const sum = use('AddLtLe', ['abs(al - x)', 'eps', 'abs(x - be)', 'eps'], c, [h1b, X.tc(c, [h2], 'abs(x - be) <= eps')]);
    return use('LeLtTrans', ['abs(al - be)', 'abs(al - x) + abs(x - be)', 'eps + eps'], c, [t, sum]);
  }));

prove('LimUnique', 'all a. all al. all be. (Conv(a,al) -> Conv(a,be) -> al = be)', '命題1.3', () => X.genAll(
  X.assume([], 'Conv(a,al)', (ha, c1) => X.assume(c1, 'Conv(a,be)', (hb, c) => {
    const ar = use('ConvR', ['a', 'al'], c, [ha]), br = use('ConvR', ['a', 'be'], c, [hb]), sq = use('ConvSeq', ['a', 'al'], c, [ha]);
    return X.raa(c, 'al = be', (hn, c2) => {
      const f = [ar, br];
      const d = 'abs(al - be)', e = 'abs(al - be) * 2^-1';
      const dp = use('AbsPos', ['al - be'], c2, [use('SubNeZero', ['al', 'be'], c2, [hn, ...f]), ...f]);
      const ep = use('HalfPos', [d], c2, [dp, ...f]);
      const tail = use('Tail', ['a', 'al', 'a', 'be', e], c2, [ha, hb, mem(c2, e, f), ep]);
      const bad = X.exE(tail, 'N', (hN, cN) => {
        const nN = X.tc(cN, [hN], 'N in Nat');
        const all = X.tc(cN, [hN], `all n. (n in Nat -> N <= n -> abs(a[n] - al) < ${e} & abs(a[n] - be) < ${e})`);
        const at = X.tc(cN, [X.inst(all, ['N']), nN, X.refl('N')], `abs(a[N] - al) < ${e} & abs(a[N] - be) < ${e}`);
        const xr = mem(cN, 'a[N]', [sq, nN]);
        const t = use('ErrTwo', ['a[N]', 'al', 'be', e], cN, [xr, ...f, mem(cN, e, f), X.tc(cN, [at], `abs(a[N] - al) < ${e}`), X.tc(cN, [at], `abs(a[N] - be) < ${e}`)]);
        const t2 = X.rw(use('HalfSum', [d], cN, f), t, `${d} < ${d}`, cN);
        return X.tc(cN, [t2, X.inst(X.thm('LtIrrefl'), [d])], '0 < 0');
      });
      return [bad, X.inst(X.thm('LtIrrefl'), ['0'])];
    });
  })), ['a', 'al', 'be']));

// ---------- 和の極限 (テキスト定理 2.1(1)) ----------
prove('ErrSum', 'all x. all y. all al. all be. all h. (x in Real -> y in Real -> al in Real -> be in Real -> h in Real -> abs(x - al) < h -> abs(y - be) < h -> abs((x + y) - (al + be)) < h + h)', '[C11]', () =>
  intro(['x', 'y', 'al', 'be', 'h'], ['abs(x - al) < h', 'abs(y - be) < h'], (c, [h1, h2]) => {
    const e = use('SubAddAdd', ['x', 'y', 'al', 'be'], c);
    const t = X.rw(X.sym(e), use('Triangle', ['x - al', 'y - be'], c), 'abs((x + y) - (al + be)) <= abs(x - al) + abs(y - be)', c);
    const s = use('AddLtLe', ['abs(x - al)', 'h', 'abs(y - be)', 'h'], c, [h1, X.tc(c, [h2], 'abs(y - be) <= h')]);
    return use('LeLtTrans', ['abs((x + y) - (al + be))', 'abs(x - al) + abs(y - be)', 'h + h'], c, [t, s]);
  }));

function convIntro(c, a, al, seqLine, alR, bodyFn) {
  // bodyFn(eps 文脈) → ctx+[eps∈ℝ, 0<eps] ⊢ ∃N(...)
  const all = X.gen(X.assume(c, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => bodyFn(c2, he, hp))), 'eps');
  return X.tc(c, [convDef(a, al), seqLine, alR, all], `Conv(${a}, ${al})`);
}

prove('LimSum', 'all a. all al. all b. all be. (Conv(a,al) -> Conv(b,be) -> Conv(oplus(a,b), al + be))', '定理2.1(1)', () => X.genAll(
  X.assume([], 'Conv(a,al)', (ha, c1) => X.assume(c1, 'Conv(b,be)', (hb, c) => {
    const sa = use('ConvSeq', ['a', 'al'], c, [ha]), sb = use('ConvSeq', ['b', 'be'], c, [hb]);
    const ar = use('ConvR', ['a', 'al'], c, [ha]), br = use('ConvR', ['b', 'be'], c, [hb]);
    const op = use('Oplus', ['a', 'b'], c, [sa, sb]);
    const sab = X.tc(c, [op], 'Seq(oplus(a,b))');
    const val = X.tc(c, [op], 'all n. (n in Nat -> oplus(a,b)[n] = a[n] + b[n])');
    return convIntro(c, 'oplus(a,b)', 'al + be', sab, mem(c, 'al + be', [ar, br]), (c2, he, hp) => {
      const h = 'eps * 2^-1';
      const hpos = use('HalfPos', ['eps'], c2, [he, hp]);
      const tail = use('Tail', ['a', 'al', 'b', 'be', h], c2, [ha, hb, mem(c2, h, [he]), hpos]);
      return X.exE(tail, 'N', (hN, cN) => {
        const nN = X.tc(cN, [hN], 'N in Nat');
        const all = X.tc(cN, [hN], `all n. (n in Nat -> N <= n -> abs(a[n] - al) < ${h} & abs(b[n] - be) < ${h})`);
        const body = X.assume(cN, 'n in Nat', (hn, cn) => X.assume(cn, 'N <= n', (hl, cl) => {
          const ab = X.tc(cl, [X.inst(all, ['n']), hn, hl], `abs(a[n] - al) < ${h} & abs(b[n] - be) < ${h}`);
          const f = [sa, sb, hn, ar, br, he];
          const s = use('ErrSum', ['a[n]', 'b[n]', 'al', 'be', h], cl, [...f, X.tc(cl, [ab], `abs(a[n] - al) < ${h}`), X.tc(cl, [ab], `abs(b[n] - be) < ${h}`)]);
          const s1 = X.rw(use('HalfSum', ['eps'], cl, [he]), s, `abs((a[n] + b[n]) - (al + be)) < eps`, cl);
          return X.rw(X.sym(X.tc(cl, [X.inst(val, ['n']), hn], 'oplus(a,b)[n] = a[n] + b[n]')), s1, 'abs(oplus(a,b)[n] - (al + be)) < eps', cl);
        }));
        const w = X.tc(cN, [nN, X.gen(body, 'n')], 'N in Nat & all n. (n in Nat -> N <= n -> abs(oplus(a,b)[n] - (al + be)) < eps)');
        return X.exI(w, 'N', 'N in Nat & all n. (n in Nat -> N <= n -> abs(oplus(a,b)[n] - (al + be)) < eps)', 'N');
      });
    });
  })), ['a', 'al', 'b', 'be']));

// ---------- 定数倍の極限 (テキスト定理 2.1(2)) ----------
prove('LimScalar', 'all c. all a. all al. (c in Real -> Conv(a,al) -> Conv(odot(c,a), c * al))', '定理2.1(2)', () => X.genAll(
  X.assume([], 'c in Real', (hc, c0) => X.assume(c0, 'Conv(a,al)', (ha, c) => {
    const sa = use('ConvSeq', ['a', 'al'], c, [ha]), ar = use('ConvR', ['a', 'al'], c, [ha]);
    const od = use('Odot', ['c', 'a'], c, [hc, sa]);
    const sca = X.tc(c, [od], 'Seq(odot(c,a))');
    const val = X.tc(c, [od], 'all n. (n in Nat -> odot(c,a)[n] = c * a[n])');
    const G = 'N in Nat & all n. (n in Nat -> N <= n -> abs(odot(c,a)[n] - c * al) < eps)';
    return convIntro(c, 'odot(c,a)', 'c * al', sca, mem(c, 'c * al', [ar]), (c2, he, hp) => {
      // |c a_n - c α| = |c| |a_n - α|
      const key = (cc, n, hn) => {
        const v = X.tc(cc, [X.inst(val, [n]), hn], `odot(c,a)[${n}] = c * a[${n}]`);
        const f = [sa, hn, ar];
        return calc(cc, `abs(odot(c,a)[${n}] - c * al)`, [
          [`abs(c * a[${n}] - c * al)`, v],
          [`abs(c * (a[${n}] - al))`, use('MulSub', ['c', `a[${n}]`, 'al'], cc, f)],
          [`abs(c) * abs(a[${n}] - al)`, use('AbsMul', ['c', `a[${n}] - al`], cc, f)],
        ]);
      };
      const zero = X.assume(c2, 'c = 0', (hz, cz) => {
        const one = X.thm('NatOne');
        const body = X.assume(cz, 'n in Nat', (hn, cn) => X.assume(cn, 'onew <= n', (hl, cl) => {
          const k = key(cl, 'n', hn);
          const az = calc(cl, 'abs(c)', [['abs(0)', hz], ['0', use('AbsOfNonneg', ['0'], cl, [X.tc(cl, [X.refl('0')], '0 <= 0')])]]);
          const z = calc(cl, `abs(c) * abs(a[n] - al)`, [['0 * abs(a[n] - al)', az], ['abs(a[n] - al) * 0', use('R7', ['0', 'abs(a[n] - al)'], cl, [sa, hn, ar])], ['0', use('Mul0', ['abs(a[n] - al)'], cl, [sa, hn, ar])]]);
          return X.rw(X.sym(X.trans(k, z, cl)), hp, 'abs(odot(c,a)[n] - c * al) < eps', cl);
        }));
        const w = X.tc(cz, [one, X.gen(body, 'n')], 'onew in Nat & all n. (n in Nat -> onew <= n -> abs(odot(c,a)[n] - c * al) < eps)');
        return X.exI(w, 'N', G, 'onew');
      });
      const nonzero = X.assume(c2, 'c != 0', (hz, cz) => {
        const cp = use('AbsPos', ['c'], cz, [hz]);
        const cr = mem(cz, 'abs(c)');
        const nz = X.neSym(use('LtNe', ['0', 'abs(c)'], cz, [cp]));
        const e2 = 'eps * abs(c)^-1';
        const e2p = use('R15', ['eps', 'abs(c)^-1'], cz, [he, hp, use('InvPos', ['abs(c)'], cz, [cr, cp]), nz]);
        const ce = use('ConvE', ['a', 'al', e2], cz, [ha, mem(cz, e2, [nz]), e2p]);
        return X.exE(ce, 'N', (hN, cN) => {
          const all = X.tc(cN, [hN], `all n. (n in Nat -> N <= n -> abs(a[n] - al) < ${e2})`);
          const body = X.assume(cN, 'n in Nat', (hn, cn) => X.assume(cn, 'N <= n', (hl, cl) => {
            const k = key(cl, 'n', hn);
            const lt = X.tc(cl, [X.inst(all, ['n']), hn, hl], `abs(a[n] - al) < ${e2}`);
            const f = [sa, hn, ar, nz, he];
            const m = use('MulLtPos', [`abs(a[n] - al)`, e2, 'abs(c)'], cl, [...f, cp, lt]);
            const simp = calc(cl, `${e2} * abs(c)`, [
              ['eps * (abs(c)^-1 * abs(c))', use('R6', ['eps', 'abs(c)^-1', 'abs(c)'], cl, f)],
              ['eps * (abs(c) * abs(c)^-1)', use('R7', ['abs(c)^-1', 'abs(c)'], cl, f)],
              ['eps * 1', use('R9', ['abs(c)'], cl, f)],
              ['eps', use('R8', ['eps'], cl, f)]]);
            const m1 = X.rw(simp, m, `abs(a[n] - al) * abs(c) < eps`, cl);
            const m2 = X.rw(use('R7', ['abs(a[n] - al)', 'abs(c)'], cl, f), m1, `abs(c) * abs(a[n] - al) < eps`, cl);
            return X.rw(X.sym(k), m2, 'abs(odot(c,a)[n] - c * al) < eps', cl);
          }));
          const w = X.tc(cN, [X.tc(cN, [hN], 'N in Nat'), X.gen(body, 'n')], G);
          return X.exI(w, 'N', G, 'N');
        });
      });
      return X.tc(c2, [zero, nonzero], `ex N. (${G})`);
    });
  })), ['c', 'a', 'al']));

// ---------- はさみうちの定理 (テキスト定理 2.3) ----------
prove('ErrSqueeze', 'all x. all y. all z. all al. all eps. (x in Real -> y in Real -> z in Real -> al in Real -> eps in Real -> x <= z -> z <= y -> abs(x - al) < eps -> abs(y - al) < eps -> abs(z - al) < eps)', '[C12]', () =>
  intro(['x', 'y', 'z', 'al', 'eps'], ['x <= z', 'z <= y', 'abs(x - al) < eps', 'abs(y - al) < eps'], (c, [h1, h2, h3, h4]) => {
    const lx = X.tc(c, [use('AbsLt', ['x - al', 'eps'], c, [h3])], '-eps < x - al');
    const ry = X.tc(c, [use('AbsLt', ['y - al', 'eps'], c, [h4])], 'y - al < eps');
    const sub = (u, v, hl) => {
      const a = use('LeAddRight', [u, v, '-al'], c, [hl]);
      const b = X.rw(X.sym(X.inst(X.defAx('minus'), [u, 'al'])), a, `${u} - al <= ${v} + -al`, c);
      return X.rw(X.sym(X.inst(X.defAx('minus'), [v, 'al'])), b, `${u} - al <= ${v} - al`, c);
    };
    const l = use('LtLeTrans', ['-eps', 'x - al', 'z - al'], c, [lx, sub('x', 'z', h1)]);
    const r = use('LeLtTrans', ['z - al', 'y - al', 'eps'], c, [sub('z', 'y', h2), ry]);
    return use('LtAbs', ['z - al', 'eps'], c, [l, r]);
  }));

prove('Squeeze', 'all a. all b. all c. all al. (Seq(c) -> (all n. (n in Nat -> a[n] <= c[n] & c[n] <= b[n])) -> Conv(a,al) -> Conv(b,al) -> Conv(c,al))', '定理2.3', () => X.genAll(
  X.assume([], 'Seq(c)', (hc, k0) => X.assume(k0, 'all n. (n in Nat -> a[n] <= c[n] & c[n] <= b[n])', (hle, k1) => X.assume(k1, 'Conv(a,al)', (ha, k2) => X.assume(k2, 'Conv(b,al)', (hb, k) => {
    const sa = use('ConvSeq', ['a', 'al'], k, [ha]), sb = use('ConvSeq', ['b', 'al'], k, [hb]), ar = use('ConvR', ['a', 'al'], k, [ha]);
    return convIntro(k, 'c', 'al', hc, ar, (c2, he, hp) => {
      const tail = use('Tail', ['a', 'al', 'b', 'al', 'eps'], c2, [ha, hb, he, hp]);
      return X.exE(tail, 'N', (hN, cN) => {
        const all = X.tc(cN, [hN], 'all n. (n in Nat -> N <= n -> abs(a[n] - al) < eps & abs(b[n] - al) < eps)');
        const body = X.assume(cN, 'n in Nat', (hn, cn) => X.assume(cn, 'N <= n', (hl, cl) => {
          const ab = X.tc(cl, [X.inst(all, ['n']), hn, hl], 'abs(a[n] - al) < eps & abs(b[n] - al) < eps');
          const le = X.tc(cl, [X.inst(hle, ['n']), hn], 'a[n] <= c[n] & c[n] <= b[n]');
          const f = [sa, sb, hc, hn, ar, he];
          return use('ErrSqueeze', ['a[n]', 'b[n]', 'c[n]', 'al', 'eps'], cl, [...f, X.tc(cl, [le], 'a[n] <= c[n]'), X.tc(cl, [le], 'c[n] <= b[n]'), X.tc(cl, [ab], 'abs(a[n] - al) < eps'), X.tc(cl, [ab], 'abs(b[n] - al) < eps')]);
        }));
        const G = 'N in Nat & all n. (n in Nat -> N <= n -> abs(c[n] - al) < eps)';
        return X.exI(X.tc(cN, [X.tc(cN, [hN], 'N in Nat'), X.gen(body, 'n')], G), 'N', G, 'N');
      });
    });
  })))), ['a', 'b', 'c', 'al']));

// ---------- 極限と大小関係 (テキスト定理 2.5) ----------
prove('LimLe', 'all a. all b. all al. all be. (Conv(a,al) -> Conv(b,be) -> (all n. (n in Nat -> a[n] <= b[n])) -> al <= be)', '定理2.5', () => X.genAll(
  X.assume([], 'Conv(a,al)', (ha, k1) => X.assume(k1, 'Conv(b,be)', (hb, k2) => X.assume(k2, 'all n. (n in Nat -> a[n] <= b[n])', (hle, k) => {
    const sa = use('ConvSeq', ['a', 'al'], k, [ha]), sb = use('ConvSeq', ['b', 'be'], k, [hb]);
    const ar = use('ConvR', ['a', 'al'], k, [ha]), br = use('ConvR', ['b', 'be'], k, [hb]);
    const notlt = X.tc(k, [X.assume(k, 'be < al', (hlt, c2) => {
      const d = 'al - be', e = '(al - be) * 2^-1';
      const f = [ar, br];
      const dp = use('SubPos', ['be', 'al'], c2, [hlt, ...f]);
      const ep = use('HalfPos', [d], c2, [dp, ...f]);
      const tail = use('Tail', ['a', 'al', 'b', 'be', e], c2, [ha, hb, mem(c2, e, f), ep]);
      const bad = X.exE(tail, 'N', (hN, cN) => {
        const nN = X.tc(cN, [hN], 'N in Nat');
        const all = X.tc(cN, [hN], `all n. (n in Nat -> N <= n -> abs(a[n] - al) < ${e} & abs(b[n] - be) < ${e})`);
        const at = X.tc(cN, [X.inst(all, ['N']), nN, X.refl('N')], `abs(a[N] - al) < ${e} & abs(b[N] - be) < ${e}`);
        const g = [sa, sb, nN, ...f];
        // α - a_N < ε
        const l1 = X.tc(cN, [use('AbsLt', ['a[N] - al', e], cN, [...g, X.tc(cN, [at], `abs(a[N] - al) < ${e}`)])], `-(${e}) < a[N] - al`);
        const l2 = X.rw(use('NegNeg', [e], cN, g), use('NegLt', [`-(${e})`, 'a[N] - al'], cN, [...g, l1]), `-(a[N] - al) < ${e}`, cN);
        const l3 = X.rw(use('SubNeg', ['al', 'a[N]'], cN, g), l2, `al - a[N] < ${e}`, cN);
        // b_N - β < ε
        const r1 = X.tc(cN, [use('AbsLt', ['b[N] - be', e], cN, [...g, X.tc(cN, [at], `abs(b[N] - be) < ${e}`)])], `b[N] - be < ${e}`);
        // a_N - b_N ≤ 0
        const ab = X.tc(cN, [X.inst(hle, ['N']), nN], 'a[N] <= b[N]');
        const m1 = X.rw(use('R5', ['b[N]'], cN, g), use('LeAddRight', ['a[N]', 'b[N]', '-b[N]'], cN, [...g, ab]), 'a[N] + -b[N] <= 0', cN);
        const m2 = X.rw(X.sym(X.inst(X.defAx('minus'), ['a[N]', 'b[N]'])), m1, 'a[N] - b[N] <= 0', cN);
        // (a_N - b_N) + (b_N - β) ≤ 0 + ε = ε
        const s1 = use('AddLeLe', ['a[N] - b[N]', '0', 'b[N] - be', e], cN, [...g, m2, X.tc(cN, [r1], `b[N] - be <= ${e}`)]);
        const z = calc(cN, `0 + ${e}`, [[`${e} + 0`, use('R3', ['0', e], cN, g)], [e, use('R4', [e], cN, g)]]);
        const s2 = X.rw(z, s1, `(a[N] - b[N]) + (b[N] - be) <= ${e}`, cN);
        const s3 = X.rw(X.sym(use('SubSplit', ['a[N]', 'be', 'b[N]'], cN, g)), s2, `a[N] - be <= ${e}`, cN);
        // α - β = (α - a_N) + (a_N - β) < ε + ε = α - β
        const t = use('AddLtLe', ['al - a[N]', e, 'a[N] - be', e], cN, [...g, l3, s3]);
        const t1 = X.rw(X.sym(use('SubSplit', ['al', 'be', 'a[N]'], cN, g)), t, `al - be < ${e} + ${e}`, cN);
        const t2 = X.rw(use('HalfSum', [d], cN, g), t1, 'al - be < al - be', cN);
        return X.tc(cN, [t2, X.inst(X.thm('LtIrrefl'), ['al - be'])], '0 < 0');
      });
      return X.tc(c2, [bad, X.inst(X.thm('LtIrrefl'), ['0'])], '~ be < al');
    })], '~ be < al');
    return use('NotLtLe', ['be', 'al'], k, [notlt, ar, br]);
  }))), ['a', 'b', 'al', 'be']));

module.exports = {};
