'use strict';
// テキスト第3章 2節(続き): 部分列, 命題2.13, 定理2.15–2.18
const K = require('./kit');
const { X, C, prove, intro, use, calc, mem, P } = K;
const { indNat, monoThm } = require('./p_nat');
const { convIntro, tailIntro, tailAt } = require('./p_seq');

// ---------------- 添字列 ----------------
const subIdx = s => X.inst(X.defAx('SubIdx'), [s]);
// 狭義単調: m < n → s_m < s_n
prove('IdxLt', 'all s. all m. (SubIdx(s) -> m in Nat -> all n. (n in Nat -> m < n -> s[m] < s[n]))', '[C16]', () => X.genAll(
  X.assume([], 'SubIdx(s)', (hs, c0) => X.assume(c0, 'm in Nat', (hm, c) => {
    const st = X.tc(c, [hs, subIdx('s')], 'all k. (k in Nat -> s[k] < s[S(k)])');
    const base = X.assume(c, 'm < onew', (h, c2) => {
      const le = use('OneLe', ['m'], c2, [hm]);
      return X.tc(c2, [use('LeNotLt', ['onew', 'm'], c2, [le]), h], 's[m] < s[onew]');
    });
    return indNat(c, 'n', 'm < n -> s[m] < s[n]', base, (c1, n, hn, hp) => X.assume(c1, 'm < S(n)', (h, c2) => {
      const le = X.tc(c2, [h], 'm <= S(n)');
      const ne = X.tc(c2, [h, X.inst(X.defAx('lt'), ['m', 'S(n)'])], 'm != S(n)');
      const cs = use('LeSCases', ['m', 'n'], c2, [use('NatOmega', ['m'], c2, [hm]), use('NatOmega', ['n'], c2, [hn]), le]);
      const sn = X.tc(c2, [X.inst(st, ['n']), hn], 's[n] < s[S(n)]');
      const a = X.assume(c2, 'm < n', (h1, c3) => use('LtTrans', ['s[m]', 's[n]', 's[S(n)]'], c3, [X.tc(c3, [hp, h1], 's[m] < s[n]'), sn]));
      const b = X.assume(c2, 'm = n', (h1, c3) => X.rw(X.sym(h1), sn, 's[m] < s[S(n)]', c3));
      return X.tc(c2, [cs, ne, a, b], 's[m] < s[S(n)]');
    }));
  })), ['s', 'm']));
// k ≤ s_k
prove('IdxGe', 'all s. (SubIdx(s) -> all k. (k in Nat -> k <= s[k]))', '[C17]', () => X.gen(X.assume([], 'SubIdx(s)', (hs, c) => {
  const ns = X.tc(c, [hs, subIdx('s')], 'NSeq(s)');
  const st = X.tc(c, [hs, subIdx('s')], 'all k. (k in Nat -> s[k] < s[S(k)])');
  const one = X.thm('NatOne');
  const base = use('OneLe', ['s[onew]'], c, [use('NSeqVal', ['s', 'onew'], c, [ns, one])]);
  return indNat(c, 'k', 'k <= s[k]', base, (c1, k, hk, hp) => {
    const sk = use('NSeqVal', ['s', 'S(k)'], c1, [ns, use('NatS', ['k'], c1, [hk])]);
    const lt = use('LeLtTrans', ['k', 's[k]', 's[S(k)]'], c1, [hp, X.tc(c1, [X.inst(st, ['k']), hk], 's[k] < s[S(k)]')]);
    return use('LtSLe', ['k', 's[S(k)]'], c1, [use('NatOmega', ['k'], c1, [hk]), use('NatOmega', ['s[S(k)]'], c1, [sk]), lt]);
  });
}), 's'));

// ---------------- 定理 6.7: 収束列の部分列 ----------------
prove('SubConvIdx', 'all a. all s. all al. (Conv(a,al) -> SubIdx(s) -> Conv(sseq(a,s), al))', '[C18]', () => X.genAll(
  X.assume([], 'Conv(a,al)', (ha, k1) => X.assume(k1, 'SubIdx(s)', (hs, k) => {
    const sa = use('ConvSeq', ['a', 'al'], k, [ha]), ar = use('ConvR', ['a', 'al'], k, [ha]);
    const ns = X.tc(k, [hs, subIdx('s')], 'NSeq(s)');
    const ss = use('SubSeqF', ['a', 's'], k, [sa, ns]);
    const ge = use('IdxGe', ['s'], k, [hs]);
    return convIntro(k, 'sseq(a,s)', 'al', X.tc(k, [ss], 'Seq(sseq(a,s))'), ar, (c2, he, hp) => X.exE(use('ConvE', ['a', 'al', 'eps'], c2, [ha, he, hp]), 'N', (hN, cN) =>
      tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `abs(sseq(a,s)[${n}] - al) < eps`, (cl, hn, hl) => {
        const sn = use('NSeqVal', ['s', 'n'], cl, [ns, hn]);
        const le = use('LeTrans', ['N', 'n', 's[n]'], cl, [hl, X.tc(cl, [X.inst(ge, ['n']), hn], 'n <= s[n]')]);
        const l = tailAt(cl, hN, 'N', n => `abs(a[${n}] - al) < eps`, 's[n]', sn, le);
        const v = X.tc(cl, [X.inst(X.tc(cl, [ss], 'all k. (k in Nat -> sseq(a,s)[k] = a[s[k]])'), ['n']), hn], 'sseq(a,s)[n] = a[s[n]]');
        return X.rw(X.sym(v), l, 'abs(sseq(a,s)[n] - al) < eps', cl);
      })));
  })), ['a', 's', 'al']));
prove('SubConv', 'all a. all b. all al. (Conv(a,al) -> SubSeq(b,a) -> Conv(b,al))', '定理6.7', () => X.genAll(
  X.assume([], 'Conv(a,al)', (ha, k1) => X.assume(k1, 'SubSeq(b,a)', (hb, k) => {
    const d = X.tc(k, [hb, X.inst(X.defAx('SubSeq'), ['b', 'a'])], 'Seq(b) & ex s. (SubIdx(s) & all k. (k in Nat -> b[k] = a[s[k]]))');
    return X.exE(X.tc(k, [d], 'ex s. (SubIdx(s) & all k. (k in Nat -> b[k] = a[s[k]]))'), 's', (hs, cs) => {
      const si = X.tc(cs, [hs], 'SubIdx(s)');
      const sa = use('ConvSeq', ['a', 'al'], cs, [ha]);
      const ss = use('SubSeqF', ['a', 's'], cs, [sa, X.tc(cs, [si, subIdx('s')], 'NSeq(s)')]);
      const eq = X.gen(X.assume(cs, 'n in Nat', (hn, cn) => {
        const v = X.tc(cn, [X.inst(X.tc(cn, [ss], 'all k. (k in Nat -> sseq(a,s)[k] = a[s[k]])'), ['n']), hn], 'sseq(a,s)[n] = a[s[n]]');
        const w = X.tc(cn, [X.inst(X.tc(cn, [hs], 'all k. (k in Nat -> b[k] = a[s[k]])'), ['n']), hn], 'b[n] = a[s[n]]');
        return X.trans(v, X.sym(w), cn);
      }), 'n');
      return use('ConvExt', ['sseq(a,s)', 'b', 'al'], cs, [X.tc(cs, [d], 'Seq(b)'), eq, use('SubConvIdx', ['a', 's', 'al'], cs, [ha, si])]);
    }, k);
  })), ['a', 'b', 'al']));

// ---------------- 命題 2.13 (奇数番目・偶数番目) ----------------
// 2つの添字列が ℕ を覆うとき, 両方の部分列が α に収束すれば元の列も α に収束する
prove('CoverConv', 'all a. all s. all t. all al. (Seq(a) -> SubIdx(s) -> SubIdx(t) -> (all n. (n in Nat -> ex k. (k in Nat & (n = s[k] | n = t[k])))) -> Conv(sseq(a,s), al) -> Conv(sseq(a,t), al) -> Conv(a, al))', '[C19]', () => X.genAll(
  X.assume([], 'Seq(a)', (sa, k1) => X.assume(k1, 'SubIdx(s)', (hs, k2) => X.assume(k2, 'SubIdx(t)', (ht, k3) =>
    X.assume(k3, 'all n. (n in Nat -> ex k. (k in Nat & (n = s[k] | n = t[k])))', (hc, k4) => X.assume(k4, 'Conv(sseq(a,s), al)', (h1, k5) => X.assume(k5, 'Conv(sseq(a,t), al)', (h2, k) => {
      const ar = use('ConvR', ['sseq(a,s)', 'al'], k, [h1]);
      const ns = X.tc(k, [hs, subIdx('s')], 'NSeq(s)'), nt = X.tc(k, [ht, subIdx('t')], 'NSeq(t)');
      const vs = X.tc(k, [use('SubSeqF', ['a', 's'], k, [sa, ns])], 'all k. (k in Nat -> sseq(a,s)[k] = a[s[k]])');
      const vt = X.tc(k, [use('SubSeqF', ['a', 't'], k, [sa, nt])], 'all k. (k in Nat -> sseq(a,t)[k] = a[t[k]])');
      return convIntro(k, 'a', 'al', sa, ar, (c2, he, hp) => X.exE(use('ConvE', ['sseq(a,s)', 'al', 'eps'], c2, [h1, he, hp]), 'N1', (q1, d1) =>
        X.exE(use('ConvE', ['sseq(a,t)', 'al', 'eps'], d1, [h2, he, hp]), 'N2', (q2, d) => {
          const n1 = X.tc(d, [q1], 'N1 in Nat'), n2 = X.tc(d, [q2], 'N2 in Nat');
          const s1 = use('NSeqVal', ['s', 'N1'], d, [ns, n1]), t2 = use('NSeqVal', ['t', 'N2'], d, [nt, n2]);
          const M = 'cup(s[N1], t[N2])';
          return tailIntro(d, M, use('NatCup', ['s[N1]', 't[N2]'], d, [s1, t2]), n => `abs(a[${n}] - al) < eps`, (cl, hn, hl) => X.exE(X.tc(cl, [X.inst(hc, ['n']), hn], 'ex k. (k in Nat & (n = s[k] | n = t[k]))'), 'k', (hk, ck) => {
            const kn = X.tc(ck, [hk], 'k in Nat');
            const branch = (u, Nu, nu, q, v, lab) => X.assume(ck, `n = ${u}[k]`, (he2, c3) => {
              const big = use('LeTrans', [`${u}[${Nu}]`, M, 'n'], c3, [X.inst(X.thm(lab), ['s[N1]', 't[N2]']), hl]);
              const tot = use('OmegaTotal', [Nu, 'k'], c3, [use('NatOmega', [Nu], c3, [nu]), use('NatOmega', ['k'], c3, [kn])]);
              const ok = X.assume(c3, `${Nu} <= k`, (hh, c4) => {
                const l = tailAt(c4, q, Nu, m => `abs(sseq(a,${u})[${m}] - al) < eps`, 'k', kn, hh);
                const v1 = X.tc(c4, [X.inst(v, ['k']), kn], `sseq(a,${u})[k] = a[${u}[k]]`);
                return X.rw(X.sym(he2), X.rw(v1, l, `abs(a[${u}[k]] - al) < eps`, c4), 'abs(a[n] - al) < eps', c4);
              });
              const bad = X.assume(c3, `k < ${Nu}`, (hh, c4) => {
                const lt = X.tc(c4, [X.inst(use('IdxLt', [u, 'k'], c4, [u === 's' ? hs : ht, kn]), [Nu]), nu, hh], `${u}[k] < ${u}[${Nu}]`);
                const lt2 = use('LtLeTrans', [`${u}[k]`, `${u}[${Nu}]`, 'n'], c4, [lt, big]);
                const lt3 = X.rw(X.sym(he2), lt2, `n < n`, c4);
                return X.tc(c4, [lt3, X.inst(X.thm('LtIrrefl'), ['n'])], 'abs(a[n] - al) < eps');
              });
              return X.tc(c3, [tot, ok, bad], 'abs(a[n] - al) < eps');
            });
            return X.tc(ck, [hk, branch('s', 'N1', n1, q1, vs, 'LeCupL'), branch('t', 'N2', n2, q2, vt, 'LeCupR')], 'abs(a[n] - al) < eps');
          }, cl));
        }, d1)));
    })))))), ['a', 's', 't', 'al']));

const evod = () => X.thm('EvOd');
const idxOf = (u) => {   // ⊢ SubIdx(u) for u ∈ {evn, odn}
  const st = X.gen(X.assume([], 'k in Nat', (hk, c) => X.tc(c, [X.inst(X.tc(c, [evod()], 'all k. (k in Nat -> evn[k] < evn[S(k)] & odn[k] < odn[S(k)])'), ['k']), hk], `${u}[k] < ${u}[S(k)]`)), 'k');
  return X.tc([], [X.inst(X.defAx('SubIdx'), [u]), evod(), st], `SubIdx(${u})`);
};
prove('OddEven', 'all a. all al. (Conv(a,al) <-> Seq(a) & Conv(sseq(a,odn), al) & Conv(sseq(a,evn), al))', '命題2.13', () => X.genAll((() => {
  const ie = idxOf('evn'), io = idxOf('odn');
  const fw = X.assume([], 'Conv(a,al)', (ha, c) => X.tc(c, [use('ConvSeq', ['a', 'al'], c, [ha]), use('SubConvIdx', ['a', 'odn', 'al'], c, [ha, io]), use('SubConvIdx', ['a', 'evn', 'al'], c, [ha, ie])],
    'Seq(a) & Conv(sseq(a,odn), al) & Conv(sseq(a,evn), al)'));
  const bw = X.assume([], 'Seq(a) & Conv(sseq(a,odn), al) & Conv(sseq(a,evn), al)', (h, c) => {
    const cov = X.tc(c, [evod()], 'all n. (n in Nat -> ex k. (k in Nat & (n = evn[k] | n = odn[k])))');
    return use('CoverConv', ['a', 'evn', 'odn', 'al'], c, [X.tc(c, [h], 'Seq(a)'), ie, io, cov, X.tc(c, [h], 'Conv(sseq(a,evn), al)'), X.tc(c, [h], 'Conv(sseq(a,odn), al)')]);
  });
  return X.tc([], [fw, bw], 'Conv(a,al) <-> Seq(a) & Conv(sseq(a,odn), al) & Conv(sseq(a,evn), al)');
})(), ['a', 'al']));

// ---------------- 定理 2.15 ----------------
prove('SubZero', 'all x. (x in Real -> x - 0 = x)', '[E28]', () => intro(['x'], [], c => calc(c, 'x - 0', [['x + -0', X.inst(X.defAx('minus'), ['x', '0'])], ['x + 0', X.thm('NegZero')], ['x', use('R4', ['x'], c)]])));
prove('AbsAbs', 'all x. (x in Real -> abs(abs(x)) = abs(x))', '[E29]', () => intro(['x'], [], c => use('AbsOfNonneg', ['abs(x)'], c, [use('AbsNonneg', ['x'], c)])));
prove('LimAbs', 'all a. all al. (Conv(a,al) -> Conv(absq(a), abs(al)))', '定理2.15(1)', () => X.genAll(X.assume([], 'Conv(a,al)', (ha, k) => {
  const sa = use('ConvSeq', ['a', 'al'], k, [ha]), ar = use('ConvR', ['a', 'al'], k, [ha]);
  const as = use('AbsSeq', ['a'], k, [sa]);
  return convIntro(k, 'absq(a)', 'abs(al)', X.tc(k, [as], 'Seq(absq(a))'), mem(k, 'abs(al)', [ar]), (c2, he, hp) => X.exE(use('ConvE', ['a', 'al', 'eps'], c2, [ha, he, hp]), 'N', (hN, cN) =>
    tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `abs(absq(a)[${n}] - abs(al)) < eps`, (cl, hn, hl) => {
      const l = tailAt(cl, hN, 'N', n => `abs(a[${n}] - al) < eps`, 'n', hn, hl);
      const r = use('LeLtTrans', ['abs(abs(a[n]) - abs(al))', 'abs(a[n] - al)', 'eps'], cl, [use('RevTriangle', ['a[n]', 'al'], cl, [sa, hn, ar]), l]);
      const v = X.tc(cl, [X.inst(X.tc(cl, [as], 'all n. (n in Nat -> absq(a)[n] = abs(a[n]))'), ['n']), hn], 'absq(a)[n] = abs(a[n])');
      return X.rw(X.sym(v), r, 'abs(absq(a)[n] - abs(al)) < eps', cl);
    })));
}), ['a', 'al']));
prove('LimAbsZero', 'all a. (Seq(a) -> (Conv(a,0) <-> Conv(absq(a), 0)))', '定理2.15(2)', () => X.gen(X.assume([], 'Seq(a)', (sa, k) => {
  const z = X.thm('R1_0');
  const az = use('AbsOfNonneg', ['0'], k, [X.tc(k, [X.refl('0')], '0 <= 0')]);
  const fw = X.assume(k, 'Conv(a,0)', (h, c) => X.rw(az, use('LimAbs', ['a', '0'], c, [h]), 'Conv(absq(a), 0)', c));
  const bw = X.assume(k, 'Conv(absq(a), 0)', (h, c) => {
    const as = use('AbsSeq', ['a'], c, [sa]);
    const eq = X.gen(X.assume(c, 'n in Nat', (hn, cn) => {
      const r = mem(cn, 'a[n]', [sa, hn]);
      const v = X.tc(cn, [X.inst(X.tc(cn, [as], 'all n. (n in Nat -> absq(a)[n] = abs(a[n]))'), ['n']), hn], 'absq(a)[n] = abs(a[n])');
      // |absq(a)_n - 0| = |a_n - 0|
      return calc(cn, 'abs(absq(a)[n] - 0)', [['abs(abs(a[n]) - 0)', v], ['abs(abs(a[n]))', use('SubZero', ['abs(a[n])'], cn, [r])], ['abs(a[n])', use('AbsAbs', ['a[n]'], cn, [r])], ['abs(a[n] - 0)', X.sym(use('SubZero', ['a[n]'], cn, [r]))]]);
    }), 'n');
    return convIntro(c, 'a', '0', sa, z, (c2, he, hp) => X.exE(use('ConvE', ['absq(a)', '0', 'eps'], c2, [h, he, hp]), 'N', (hN, cN) =>
      tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `abs(a[${n}] - 0) < eps`, (cl, hn, hl) =>
        X.rw(X.tc(cl, [X.inst(eq, ['n']), hn], 'abs(absq(a)[n] - 0) = abs(a[n] - 0)'), tailAt(cl, hN, 'N', n => `abs(absq(a)[${n}] - 0) < eps`, 'n', hn, hl), 'abs(a[n] - 0) < eps', cl))));
  });
  return X.tc(k, [fw, bw], 'Conv(a,0) <-> Conv(absq(a), 0)');
}), 'a'));
prove('LimSubConst', 'all a. all al. (Seq(a) -> al in Real -> (Conv(a,al) <-> Conv(oplus(a, cseq(-al)), 0)))', '定理2.15(3)', () => X.genAll(X.assume([], 'Seq(a)', (sa, k0) => X.assume(k0, 'al in Real', (ar, k) => {
  const cs = use('ConstSeq', ['-al'], k, [mem(k, '-al', [ar])]);
  const sc = X.tc(k, [cs], 'Seq(cseq(-al))');
  const op = use('Oplus', ['a', 'cseq(-al)'], k, [sa, sc]);
  const so = X.tc(k, [op], 'Seq(oplus(a, cseq(-al)))');
  const eq = X.gen(X.assume(k, 'n in Nat', (hn, cn) => {
    const v = X.tc(cn, [X.inst(X.tc(cn, [op], 'all n. (n in Nat -> oplus(a, cseq(-al))[n] = a[n] + cseq(-al)[n])'), ['n']), hn], 'oplus(a, cseq(-al))[n] = a[n] + cseq(-al)[n]');
    const w = X.tc(cn, [X.inst(X.tc(cn, [cs], 'all n. (n in Nat -> cseq(-al)[n] = -al)'), ['n']), hn], 'cseq(-al)[n] = -al');
    const r = mem(cn, 'a[n]', [sa, hn]);
    return calc(cn, 'abs(oplus(a, cseq(-al))[n] - 0)', [['abs((a[n] + cseq(-al)[n]) - 0)', v], ['abs((a[n] + -al) - 0)', w], ['abs(a[n] + -al)', use('SubZero', ['a[n] + -al'], cn, [r, ar])], ['abs(a[n] - al)', X.sym(X.inst(X.defAx('minus'), ['a[n]', 'al']))]]);
  }), 'n');
  const z = X.thm('R1_0');
  const fw = X.assume(k, 'Conv(a,al)', (h, c) => convIntro(c, 'oplus(a, cseq(-al))', '0', so, z, (c2, he, hp) => X.exE(use('ConvE', ['a', 'al', 'eps'], c2, [h, he, hp]), 'N', (hN, cN) =>
    tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `abs(oplus(a, cseq(-al))[${n}] - 0) < eps`, (cl, hn, hl) =>
      X.rw(X.sym(X.tc(cl, [X.inst(eq, ['n']), hn], 'abs(oplus(a, cseq(-al))[n] - 0) = abs(a[n] - al)')), tailAt(cl, hN, 'N', n => `abs(a[${n}] - al) < eps`, 'n', hn, hl), 'abs(oplus(a, cseq(-al))[n] - 0) < eps', cl)))));
  const bw = X.assume(k, 'Conv(oplus(a, cseq(-al)), 0)', (h, c) => convIntro(c, 'a', 'al', sa, ar, (c2, he, hp) => X.exE(use('ConvE', ['oplus(a, cseq(-al))', '0', 'eps'], c2, [h, he, hp]), 'N', (hN, cN) =>
    tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `abs(a[${n}] - al) < eps`, (cl, hn, hl) =>
      X.rw(X.tc(cl, [X.inst(eq, ['n']), hn], 'abs(oplus(a, cseq(-al))[n] - 0) = abs(a[n] - al)'), tailAt(cl, hN, 'N', n => `abs(oplus(a, cseq(-al))[${n}] - 0) < eps`, 'n', hn, hl), 'abs(a[n] - al) < eps', cl)))));
  return X.tc(k, [fw, bw], 'Conv(a,al) <-> Conv(oplus(a, cseq(-al)), 0)');
})), ['a', 'al']));

// ---------------- 定理 2.16–2.18 (∞ への発散) ----------------
const dvgDef = a => X.inst(X.defAx('DvgP'), [a]);
const DG = (a, Kt) => `ex N. (N in Nat & all n. (n in Nat -> N <= n -> ${Kt} < ${a}[n]))`;
function dvgIntro(c, a, seqLine, bodyFn) {
  const all = X.gen(X.assume(c, 'K in Real', (hK, c1) => X.assume(c1, '0 < K', (hp, c2) => bodyFn(c2, hK, hp))), 'K');
  return X.tc(c, [dvgDef(a), seqLine, all], `DvgP(${a})`);
}
const dvgE = (c, a, h, Kt, hK, hp) => X.tc(c, [X.inst(X.tc(c, [h, dvgDef(a)], `all K. (K in Real -> 0 < K -> ${DG(a, 'K')})`), [Kt]), hK, hp], DG(a, Kt));
prove('InvInv', 'all x. (x in Real -> x != 0 -> (x^-1)^-1 = x)', '[E30]', () => intro(['x'], ['x != 0'], (c, [hx]) =>
  X.sym(use('InvUnique', ['x^-1', 'x'], c, [hx, use('InvNe0', ['x'], c, [hx]), use('InvMulL', ['x'], c, [hx])]))));

prove('DvgRecip', 'all a. (DvgP(a) -> (all n. (n in Nat -> a[n] != 0)) -> Conv(recip(a), 0))', '定理2.16', () => X.gen(
  X.assume([], 'DvgP(a)', (ha, k1) => X.assume(k1, 'all n. (n in Nat -> a[n] != 0)', (hz, k) => {
    const sa = X.tc(k, [ha, dvgDef('a')], 'Seq(a)');
    const rc = use('Recip', ['a'], k, [sa, hz]);
    return convIntro(k, 'recip(a)', '0', X.tc(k, [rc], 'Seq(recip(a))'), X.thm('R1_0'), (c2, he, hp) => {
      const en = X.neSym(use('LtNe', ['0', 'eps'], c2, [hp]));
      const ip = use('InvPos', ['eps'], c2, [he, hp]);
      return X.exE(dvgE(c2, 'a', ha, 'eps^-1', mem(c2, 'eps^-1', [he, en]), ip), 'N', (hN, cN) =>
        tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `abs(recip(a)[${n}] - 0) < eps`, (cl, hn, hl) => {
          const f = [sa, hn, he, en];
          const big = tailAt(cl, hN, 'N', n => `eps^-1 < a[${n}]`, 'n', hn, hl);
          const apos = use('LtTrans', ['0', 'eps^-1', 'a[n]'], cl, [ip, big]);
          const anz = X.tc(cl, [X.inst(hz, ['n']), hn], 'a[n] != 0');
          const il = X.rw(use('InvInv', ['eps'], cl, f), use('InvLt', ['eps^-1', 'a[n]'], cl, [...f, mem(cl, 'eps^-1', f), ip, big]), 'a[n]^-1 < eps', cl);
          const ipos = use('InvPos', ['a[n]'], cl, [...f, apos]);
          const ab = calc(cl, 'abs(a[n]^-1 - 0)', [['abs(a[n]^-1)', use('SubZero', ['a[n]^-1'], cl, [...f, anz])], ['a[n]^-1', use('AbsOfNonneg', ['a[n]^-1'], cl, [X.tc(cl, [ipos], '0 <= a[n]^-1')])]]);
          const r = X.rw(X.sym(ab), il, 'abs(a[n]^-1 - 0) < eps', cl);
          const v = X.tc(cl, [X.inst(X.tc(cl, [rc], 'all n. (n in Nat -> recip(a)[n] = a[n]^-1)'), ['n']), hn], 'recip(a)[n] = a[n]^-1');
          return X.rw(X.sym(v), r, 'abs(recip(a)[n] - 0) < eps', cl);
        }));
    });
  })), 'a'));

prove('RecipDvg', 'all a. ((all n. (n in Nat -> 0 < a[n])) -> Conv(a,0) -> DvgP(recip(a)))', '定理2.17', () => X.gen(
  X.assume([], 'all n. (n in Nat -> 0 < a[n])', (hp0, k1) => X.assume(k1, 'Conv(a,0)', (ha, k) => {
    const sa = use('ConvSeq', ['a', '0'], k, [ha]);
    const nz = X.gen(X.assume(k, 'n in Nat', (hn, cn) => X.neSym(use('LtNe', ['0', 'a[n]'], cn, [X.tc(cn, [X.inst(hp0, ['n']), hn], '0 < a[n]')]))), 'n');
    const rc = use('Recip', ['a'], k, [sa, nz]);
    return dvgIntro(k, 'recip(a)', X.tc(k, [rc], 'Seq(recip(a))'), (c2, hK, hp) => {
      const kn = X.neSym(use('LtNe', ['0', 'K'], c2, [hp]));
      const ip = use('InvPos', ['K'], c2, [hK, hp]);
      return X.exE(use('ConvE', ['a', '0', 'K^-1'], c2, [ha, mem(c2, 'K^-1', [hK, kn]), ip]), 'N', (hN, cN) =>
        tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `K < recip(a)[${n}]`, (cl, hn, hl) => {
          const f = [sa, hn, hK, kn];
          const l = tailAt(cl, hN, 'N', n => `abs(a[${n}] - 0) < K^-1`, 'n', hn, hl);
          const apos = X.tc(cl, [X.inst(hp0, ['n']), hn], '0 < a[n]');
          const ab = calc(cl, 'abs(a[n] - 0)', [['abs(a[n])', use('SubZero', ['a[n]'], cl, f)], ['a[n]', use('AbsOfNonneg', ['a[n]'], cl, [X.tc(cl, [apos], '0 <= a[n]')])]]);
          const l2 = X.rw(ab, l, 'a[n] < K^-1', cl);
          const il = X.rw(use('InvInv', ['K'], cl, f), use('InvLt', ['a[n]', 'K^-1'], cl, [...f, mem(cl, 'K^-1', f), apos, l2]), 'K < a[n]^-1', cl);
          const v = X.tc(cl, [X.inst(X.tc(cl, [rc], 'all n. (n in Nat -> recip(a)[n] = a[n]^-1)'), ['n']), hn], 'recip(a)[n] = a[n]^-1');
          return X.rw(X.sym(v), il, 'K < recip(a)[n]', cl);
        }));
    });
  })), 'a'));

prove('DvgLe', 'all a. all b. (DvgP(a) -> Seq(b) -> (all n. (n in Nat -> a[n] <= b[n])) -> DvgP(b))', '定理2.18(1)', () => X.genAll(
  X.assume([], 'DvgP(a)', (ha, k1) => X.assume(k1, 'Seq(b)', (sb, k2) => X.assume(k2, 'all n. (n in Nat -> a[n] <= b[n])', (hl0, k) =>
    dvgIntro(k, 'b', sb, (c2, hK, hp) => X.exE(dvgE(c2, 'a', ha, 'K', hK, hp), 'N', (hN, cN) =>
      tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `K < b[${n}]`, (cl, hn, hl) =>
        use('LtLeTrans', ['K', 'a[n]', 'b[n]'], cl, [tailAt(cl, hN, 'N', n => `K < a[${n}]`, 'n', hn, hl), X.tc(cl, [X.inst(hl0, ['n']), hn], 'a[n] <= b[n]')]))))))), ['a', 'b']));

prove('DvgAdd', 'all a. all b. all C. (DvgP(a) -> Seq(b) -> C in Real -> (all n. (n in Nat -> C <= b[n])) -> DvgP(oplus(a,b)))', '定理2.18(2)', () => X.genAll(
  X.assume([], 'DvgP(a)', (ha, k1) => X.assume(k1, 'Seq(b)', (sb, k2) => X.assume(k2, 'C in Real', (hC, k3) => X.assume(k3, 'all n. (n in Nat -> C <= b[n])', (hb0, k) => {
    const sa = X.tc(k, [ha, dvgDef('a')], 'Seq(a)');
    const op = use('Oplus', ['a', 'b'], k, [sa, sb]);
    return dvgIntro(k, 'oplus(a,b)', X.tc(k, [op], 'Seq(oplus(a,b))'), (c2, hK, hp) => {
      const f = [sa, sb, hC, hK];
      const K1 = 'abs(K - C) + 1';
      const k1p = use('LeLtTrans', ['0', 'abs(K - C)', K1], c2, [use('AbsNonneg', ['K - C'], c2, f), use('LtAddOne', ['abs(K - C)'], c2, f)]);
      return X.exE(dvgE(c2, 'a', ha, K1, mem(c2, K1, f), k1p), 'N', (hN, cN) =>
        tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `K < oplus(a,b)[${n}]`, (cl, hn, hl) => {
          const g = [...f, hn];
          const big = tailAt(cl, hN, 'N', n => `${K1} < a[${n}]`, 'n', hn, hl);
          const kc = X.tc(cl, [use('AbsBound', ['K - C'], cl, g)], 'K - C <= abs(K - C)');
          const l1 = use('LeLtTrans', ['K - C', 'abs(K - C)', 'a[n]'], cl, [kc, use('LtTrans', ['abs(K - C)', K1, 'a[n]'], cl, [use('LtAddOne', ['abs(K - C)'], cl, g), big])]);
          const l2 = use('AddLtLe', ['K - C', 'a[n]', 'C', 'b[n]'], cl, [...g, l1, X.tc(cl, [X.inst(hb0, ['n']), hn], 'C <= b[n]')]);
          const l3 = X.rw(use('SubAdd', ['K', 'C'], cl, g), l2, 'K < a[n] + b[n]', cl);
          const v = X.tc(cl, [X.inst(X.tc(cl, [op], 'all n. (n in Nat -> oplus(a,b)[n] = a[n] + b[n])'), ['n']), hn], 'oplus(a,b)[n] = a[n] + b[n]');
          return X.rw(X.sym(v), l3, 'K < oplus(a,b)[n]', cl);
        }));
    });
  })))), ['a', 'b', 'C']));

prove('DvgMul', 'all a. all b. all C. (DvgP(a) -> Seq(b) -> C in Real -> 0 < C -> (all n. (n in Nat -> C <= b[n])) -> DvgP(otimes(a,b)))', '定理2.18(3)', () => X.genAll(
  X.assume([], 'DvgP(a)', (ha, k1) => X.assume(k1, 'Seq(b)', (sb, k2) => X.assume(k2, 'C in Real', (hC, k3) => X.assume(k3, '0 < C', (hCp, k4) => X.assume(k4, 'all n. (n in Nat -> C <= b[n])', (hb0, k) => {
    const sa = X.tc(k, [ha, dvgDef('a')], 'Seq(a)');
    const ot = use('Otimes', ['a', 'b'], k, [sa, sb]);
    const cn = X.neSym(use('LtNe', ['0', 'C'], k, [hCp]));
    return dvgIntro(k, 'otimes(a,b)', X.tc(k, [ot], 'Seq(otimes(a,b))'), (c2, hK, hp) => {
      const f = [sa, sb, hC, hK, cn];
      const K1 = 'K * C^-1';
      const k1p = use('R15', ['K', 'C^-1'], c2, [...f, hp, use('InvPos', ['C'], c2, [...f, hCp])]);
      return X.exE(dvgE(c2, 'a', ha, K1, mem(c2, K1, f), k1p), 'N', (hN, cN) =>
        tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `K < otimes(a,b)[${n}]`, (cl, hn, hl) => {
          const g = [...f, hn];
          const big = tailAt(cl, hN, 'N', n => `${K1} < a[${n}]`, 'n', hn, hl);
          const apos = use('LtTrans', ['0', K1, 'a[n]'], cl, [k1p, big]);
          const l1 = X.rw(use('DivMul', ['K', 'C'], cl, g), use('MulLtPos', [K1, 'a[n]', 'C'], cl, [...g, hCp, big]), 'K < a[n] * C', cl);
          const l2 = use('MulLeNonnegL', ['C', 'b[n]', 'a[n]'], cl, [...g, X.tc(cl, [apos], '0 <= a[n]'), X.tc(cl, [X.inst(hb0, ['n']), hn], 'C <= b[n]')]);
          const l3 = use('LtLeTrans', ['K', 'a[n] * C', 'a[n] * b[n]'], cl, [l1, l2]);
          const v = X.tc(cl, [X.inst(X.tc(cl, [ot], 'all n. (n in Nat -> otimes(a,b)[n] = a[n] * b[n])'), ['n']), hn], 'otimes(a,b)[n] = a[n] * b[n]');
          return X.rw(X.sym(v), l3, 'K < otimes(a,b)[n]', cl);
        }));
    });
  }))))), ['a', 'b', 'C']));

module.exports = { dvgIntro, dvgE, idxOf };
