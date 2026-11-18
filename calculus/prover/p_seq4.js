'use strict';
// テキスト第3章 6節: Bolzano–Weierstrass の定理, Cauchy 列と実数の完備性
const K = require('./kit');
const { X, C, prove, intro, use, calc, mem, P } = K;
const { convIntro, tailIntro, tailAt } = require('./p_seq');
require('./p_seq3');

const supDef = (s, E) => X.inst(X.defAx('IsSup'), [s, E]);
const ubDef = (b, E) => X.inst(X.defAx('UB'), [b, E]);

// 1 < ι(K)·ε → ι(K)^{-1} < ε
prove('ArchInv', 'all eps. (eps in Real -> 0 < eps -> ex K. (K in Nat & iota(K)^-1 < eps))', '[C24]', () => intro(['eps'], ['0 < eps'], (c, [hp]) => {
  const one = X.tc(c, [X.thm('ZeroLtOne')], '0 < 1');
  return X.exE(use('Archimedes', ['eps', '1'], c, [X.thm('R1_1'), hp, one]), 'K', (hK, cK) => {
    const kn = X.tc(cK, [hK], 'K in Nat');
    const ip = use('IotaPos', ['K'], cK, [kn]);
    const f = [kn];
    const l = X.rw(use('R7', ['iota(K)', 'eps'], cK, f), X.tc(cK, [hK], '1 < iota(K) * eps'), '1 < eps * iota(K)', cK);
    const d = use('LtDiv', ['1', 'iota(K)', 'eps'], cK, [...f, ip, l]);
    const nz = X.neSym(use('LtNe', ['0', 'iota(K)'], cK, [ip]));
    const e = calc(cK, '1 * iota(K)^-1', [['iota(K)^-1 * 1', use('R7', ['1', 'iota(K)^-1'], cK, [...f, nz])], ['iota(K)^-1', use('R8', ['iota(K)^-1'], cK, [...f, nz])]]);
    return X.exI(X.tc(cK, [kn, X.rw(e, d, 'iota(K)^-1 < eps', cK)], 'K in Nat & iota(K)^-1 < eps'), 'K', 'K in Nat & iota(K)^-1 < eps', 'K');
  });
}));
// K ≤ n → ι(n)^{-1} ≤ ι(K)^{-1}
prove('IotaInvMono', 'all K. all n. (K in Nat -> n in Nat -> K <= n -> iota(n)^-1 <= iota(K)^-1)', '[C25]', () => X.genAll(
  X.assume([], 'K in Nat', (hK, c1) => X.assume(c1, 'n in Nat', (hn, c2) => X.assume(c2, 'K <= n', (hl, c) =>
    use('InvLe', ['iota(K)', 'iota(n)'], c, [hK, hn, use('IotaPos', ['K'], c, [hK]), use('IotaMono', ['K', 'n'], c, [hK, hn, hl])])))), ['K', 'n']));

// ---------------- 定理 6.8: Bolzano–Weierstrass ----------------
const PHI = x => `all N. (N in Nat -> ex n. (n in Nat & N <= n & ${x} <= a[n]))`;
prove('BW', 'all a. (SeqBdd(a) -> ex b. (SubSeq(b,a) & Cgt(b)))', '定理6.8', () => X.gen(X.assume([], 'SeqBdd(a)', (hb, k) => {
  const d = X.tc(k, [hb, X.inst(X.defAx('SeqBdd'), ['a'])], 'Seq(a) & ex M. (M in Real & all n. (n in Nat -> abs(a[n]) <= M))');
  const sa = X.tc(k, [d], 'Seq(a)');
  return X.exE(X.tc(k, [d], 'ex M. (M in Real & all n. (n in Nat -> abs(a[n]) <= M))'), 'M', (hM, cM) => {
    const mr = X.tc(cM, [hM], 'M in Real');
    const bnd = (c, n, hn) => use('AbsLe', [`a[${n}]`, 'M'], c, [sa, hn, mr, X.tc(c, [X.inst(X.tc(c, [hM], 'all n. (n in Nat -> abs(a[n]) <= M)'), [n]), hn], `abs(a[${n}]) <= M`)]);
    const sep = X.inst(X.axiom('Sep', `all a. all A. ex E. all x. (x in E <-> x in A & ${PHI('x')})`), ['a', 'Real']);
    return X.exE(sep, 'E', (hE, cE) => {
      const dE = t => X.inst(hE, [t]);
      const es = X.tc(cE, [X.inst(X.defAx('sub'), ['E', 'Real']), X.gen(X.assume(cE, 'u in E', (hu, cu) => X.tc(cu, [dE('u'), hu], 'u in Real')), 'u')], 'E sub Real');
      // -M ∈ E
      const pm = X.gen(X.assume(cE, 'N in Nat', (hN, cN) => X.exI(X.tc(cN, [hN, X.refl('N'), bnd(cN, 'N', hN)], 'N in Nat & N <= N & -M <= a[N]'), 'n', 'n in Nat & N <= n & -M <= a[n]', 'N')), 'N');
      const mE = X.tc(cE, [dE('-M'), mem(cE, '-M', [mr]), pm], '-M in E');
      const ne = use('ExNonempty', ['E', '-M'], cE, [mE]);
      // M は E の上界
      const one = X.thm('NatOne');
      const ub = X.tc(cE, [ubDef('M', 'E'), mr, X.gen(X.assume(cE, 'x in E', (hx, cx) => {
        const ph = X.tc(cx, [dE('x'), hx], PHI('x'));
        return X.exE(X.tc(cx, [X.inst(ph, ['onew']), one], 'ex n. (n in Nat & onew <= n & x <= a[n])'), 'n', (hn, cn) => {
          const nn = X.tc(cn, [hn], 'n in Nat');
          return use('LeTrans', ['x', 'a[n]', 'M'], cn, [X.tc(cn, [hn], 'x <= a[n]'), X.tc(cn, [bnd(cn, 'n', nn)], 'a[n] <= M')]);
        }, cx);
      }), 'x')], 'UB(M, E)');
      return X.exE(use('R16', ['E'], cE, [es, ne, X.exI(ub, 'b', 'UB(b, E)', 'M')]), 'c', (hc, cc) => {
        const cr = X.tc(cc, [hc, supDef('c', 'E'), ubDef('c', 'E')], 'c in Real');
        const ubc = X.tc(cc, [hc, supDef('c', 'E'), ubDef('c', 'E')], 'all x. (x in E -> x <= c)');
        // c は集積点: ∀k ∀N ∃n≥N |a_n - c| < ι(k)^{-1}
        const CLk = 'all N. (N in Nat -> ex n. (n in Nat & N <= n & abs(a[n] - c) < iota(k)^-1))';
        const cl = X.gen(X.assume(cc, 'k in Nat', (hk, ck) => {
          const e = 'iota(k)^-1';
          const kp = use('IotaPos', ['k'], ck, [hk]);
          const kz = X.neSym(use('LtNe', ['0', 'iota(k)'], ck, [kp]));
          const f = [cr, hk, kz];
          const ep = use('InvPos', ['iota(k)'], ck, [...f, kp]);
          const er = mem(ck, e, f);
          // (i) c + e ∉ E
          const notIn = X.raa(ck, '~ c + e in E'.replace('e', e), (hn, c2) => {
            const inE = X.tc(c2, [hn], `c + ${e} in E`);
            const le = X.tc(c2, [X.inst(ubc, [`c + ${e}`]), inE], `c + ${e} <= c`);
            return [use('LtAddPos', ['c', e], c2, [...f, er, ep]), use('LeNotLt', [`c + ${e}`, 'c'], c2, [le])];
          });
          const notPhi = X.tc(ck, [notIn, dE(`c + ${e}`), mem(ck, `c + ${e}`, f)], `~ ${PHI(`c + ${e}`)}`);
          return X.exE(X.notAllToEx(notPhi), 'N1', (hN1, c1) => {
            const n1 = X.tc(c1, [hN1], 'N1 in Nat');
            const never = X.tc(c1, [hN1], `all n. ~(n in Nat & N1 <= n & c + ${e} <= a[n])`);
            // (ii) c - e < x となる x ∈ E
            return X.exE(use('SupApprox', ['c', 'E', e], c1, [es, hc, er, ep]), 'x', (hx, c3) => {
              const xE = X.tc(c3, [hx], 'x in E');
              const ph = X.tc(c3, [dE('x'), xE], PHI('x'));
              return X.gen(X.assume(c3, 'N in Nat', (hN, c4) => {
                const M2 = 'cup(N, N1)';
                const m2 = use('NatCup', ['N', 'N1'], c4, [hN, n1]);
                return X.exE(X.tc(c4, [X.inst(ph, [M2]), m2], `ex n. (n in Nat & ${M2} <= n & x <= a[n])`), 'n', (hn, c5) => {
                  const nn = X.tc(c5, [hn], 'n in Nat');
                  const g = [...f, sa, nn, er];
                  const le1 = use('LeTrans', ['N', M2, 'n'], c5, [X.inst(X.thm('LeCupL'), ['N', 'N1']), X.tc(c5, [hn], `${M2} <= n`)]);
                  const le2 = use('LeTrans', ['N1', M2, 'n'], c5, [X.inst(X.thm('LeCupR'), ['N', 'N1']), X.tc(c5, [hn], `${M2} <= n`)]);
                  const nl = X.tc(c5, [X.inst(never, ['n']), nn, le2], `~ c + ${e} <= a[n]`);
                  const up = use('NotLeLt', ['a[n]', `c + ${e}`], c5, [...g, nl]);
                  const lo = use('LtLeTrans', [`c - ${e}`, 'x', 'a[n]'], c5, [X.tc(c5, [hx], `c - ${e} < x`), X.tc(c5, [hn], 'x <= a[n]')]);
                  const ab = use('BandAbs', ['c', e, 'a[n]'], c5, [...g, lo, up]);
                  return X.exI(X.tc(c5, [nn, le1, ab], `n in Nat & N <= n & abs(a[n] - c) < ${e}`), 'n', `n in Nat & N <= n & abs(a[n] - c) < ${e}`, 'n');
                }, c4);
              }), 'N');
            }, c1);
          }, ck);
        }), 'k');
        // 部分列の抽出
        return X.exE(use('ExtractSub', ['a', 'c'], cc, [sa, cl]), 's', (hs, cs) => {
          const si = X.tc(cs, [hs], 'SubIdx(s)');
          const ns = X.tc(cs, [si, X.inst(X.defAx('SubIdx'), ['s'])], 'NSeq(s)');
          const ss = use('SubSeqF', ['a', 's'], cs, [sa, ns]);
          const val = X.tc(cs, [ss], 'all k. (k in Nat -> sseq(a,s)[k] = a[s[k]])');
          const near = X.tc(cs, [hs], 'all k. (k in Nat -> abs(a[s[k]] - c) < iota(k)^-1)');
          const conv = convIntro(cs, 'sseq(a,s)', 'c', X.tc(cs, [ss], 'Seq(sseq(a,s))'), cr, (c2, he, hp) => X.exE(use('ArchInv', ['eps'], c2, [he, hp]), 'K', (hK, cK) => {
            const kn = X.tc(cK, [hK], 'K in Nat');
            return tailIntro(cK, 'K', kn, n => `abs(sseq(a,s)[${n}] - c) < eps`, (cl2, hn, hl) => {
              const lt = X.tc(cl2, [X.inst(near, ['n']), hn], 'abs(a[s[n]] - c) < iota(n)^-1');
              const le = use('IotaInvMono', ['K', 'n'], cl2, [kn, hn, hl]);
              const r = use('LtTrans', ['abs(a[s[n]] - c)', 'iota(K)^-1', 'eps'], cl2, [use('LtLeTrans', ['abs(a[s[n]] - c)', 'iota(n)^-1', 'iota(K)^-1'], cl2, [lt, le]), X.tc(cl2, [hK], 'iota(K)^-1 < eps')]);
              return X.rw(X.sym(X.tc(cl2, [X.inst(val, ['n']), hn], 'sseq(a,s)[n] = a[s[n]]')), r, 'abs(sseq(a,s)[n] - c) < eps', cl2);
            });
          }));
          const sub = X.tc(cs, [X.inst(X.defAx('SubSeq'), ['sseq(a,s)', 'a']), X.tc(cs, [ss], 'Seq(sseq(a,s))'),
            X.exI(X.tc(cs, [si, val], 'SubIdx(s) & all k. (k in Nat -> sseq(a,s)[k] = a[s[k]])'), 't', 'SubIdx(t) & all k. (k in Nat -> sseq(a,s)[k] = a[t[k]])', 's')], 'SubSeq(sseq(a,s), a)');
          const cgt = X.tc(cs, [X.inst(X.defAx('Cgt'), ['sseq(a,s)']), X.exI(conv, 'al', 'Conv(sseq(a,s), al)', 'c')], 'Cgt(sseq(a,s))');
          return X.exI(X.tc(cs, [sub, cgt], 'SubSeq(sseq(a,s), a) & Cgt(sseq(a,s))'), 'b', 'SubSeq(b,a) & Cgt(b)', 'sseq(a,s)');
        }, cc);
      }, cE);
    }, cM);
  }, k);
}), 'a'));

// ---------------- Cauchy 列 ----------------
const CQ = (a, e) => `ex N. (N in Nat & all m. all n. (m in Nat -> n in Nat -> N <= m -> N <= n -> abs(${a}[m] - ${a}[n]) < ${e}))`;
prove('CauchyE', `all a. all eps. (Cauchy(a) -> eps in Real -> 0 < eps -> ${CQ('a', 'eps')})`, '[C26]', () => X.genAll(
  X.assume([], 'Cauchy(a)', (h, c1) => X.assume(c1, 'eps in Real', (he, c2) => X.assume(c2, '0 < eps', (hp, c) =>
    X.tc(c, [X.inst(X.tc(c, [h, X.inst(X.defAx('Cauchy'), ['a'])], `all eps. (eps in Real -> 0 < eps -> ${CQ('a', 'eps')})`), ['eps']), he, hp], CQ('a', 'eps'))))), ['a', 'eps']));
prove('ErrChain', 'all x. all y. all z. all e. (x in Real -> y in Real -> z in Real -> e in Real -> abs(x - y) < e -> abs(y - z) < e -> abs(x - z) < e + e)', '[C27]', () =>
  intro(['x', 'y', 'z', 'e'], ['abs(x - y) < e', 'abs(y - z) < e'], (c, [h1, h2]) => {
    const t = X.rw(X.sym(use('SubSplit', ['x', 'z', 'y'], c)), use('Triangle', ['x - y', 'y - z'], c), 'abs(x - z) <= abs(x - y) + abs(y - z)', c);
    return use('LeLtTrans', ['abs(x - z)', 'abs(x - y) + abs(y - z)', 'e + e'], c, [t, use('AddLtLt', ['abs(x - y)', 'e', 'abs(y - z)', 'e'], c, [h1, h2])]);
  }));

prove('CauchyBdd', 'all a. (Cauchy(a) -> SeqBdd(a))', '補題6.10', () => X.gen(X.assume([], 'Cauchy(a)', (ha, k) => {
  const sa = X.tc(k, [ha, X.inst(X.defAx('Cauchy'), ['a'])], 'Seq(a)');
  const one = X.tc(k, [X.thm('ZeroLtOne')], '0 < 1');
  return X.exE(use('CauchyE', ['a', '1'], k, [ha, X.thm('R1_1'), one]), 'N', (hN, cN) => {
    const nN = X.tc(cN, [hN], 'N in Nat');
    const cq = X.tc(cN, [hN], 'all m. all n. (m in Nat -> n in Nat -> N <= m -> N <= n -> abs(a[m] - a[n]) < 1)');
    return X.exE(X.tc(cN, [X.inst(use('FinBound', ['a'], cN, [sa]), ['N']), nN], 'ex M. (M in Real & 0 <= M & all n. (n in Nat -> n <= N -> abs(a[n]) <= M))'), 'M', (hM, cM) => {
      const mr = X.tc(cM, [hM], 'M in Real'), m0 = X.tc(cM, [hM], '0 <= M');
      const aN = 'a[N]';
      const A = `1 + abs(${aN})`, B = `M + (${A})`;
      const f = [sa, nN, mr];
      const a0 = use('AddNonnegNonneg', ['1', `abs(${aN})`], cM, [...f, X.tc(cM, [one], '0 <= 1'), use('AbsNonneg', [aN], cM, f)]);
      const nn = X.gen(X.assume(cM, 'n in Nat', (hn, c1) => {
        const g = [...f, hn];
        const cs = use('OmegaTotal', ['N', 'n'], c1, [use('NatOmega', ['N'], c1, [nN]), use('NatOmega', ['n'], c1, [hn])]);
        const big = X.assume(c1, 'N <= n', (hl, c2) => {
          const dd = X.tc(c2, [X.inst(cq, ['n', 'N']), hn, nN, hl, X.tc(c2, [X.refl('N')], 'N <= N')], `abs(a[n] - ${aN}) < 1`);
          const t = X.rw(use('SubAdd', ['a[n]', aN], c2, g), use('Triangle', [`a[n] - ${aN}`, aN], c2, g), `abs(a[n]) <= abs(a[n] - ${aN}) + abs(${aN})`, c2);
          const s = use('AddLtLe', [`abs(a[n] - ${aN})`, '1', `abs(${aN})`, `abs(${aN})`], c2, [...g, dd, X.tc(c2, [X.refl(`abs(${aN})`)], `abs(${aN}) <= abs(${aN})`)]);
          const l = X.tc(c2, [use('LeLtTrans', ['abs(a[n])', `abs(a[n] - ${aN}) + abs(${aN})`, A], c2, [...g, t, s])], `abs(a[n]) <= ${A}`);
          return use('LeTrans', ['abs(a[n])', A, B], c2, [l, use('LeAddNonnegL', [A, 'M'], c2, [...g, m0])]);
        });
        const small = X.assume(c1, 'n < N', (hl, c2) => {
          const b = X.tc(c2, [X.inst(X.tc(c2, [hM], 'all n. (n in Nat -> n <= N -> abs(a[n]) <= M)'), ['n']), hn, hl], 'abs(a[n]) <= M');
          return use('LeTrans', ['abs(a[n])', 'M', B], c2, [b, use('LeAddNonneg', ['M', A], c2, [...g, a0])]);
        });
        return X.tc(c1, [cs, big, small], `abs(a[n]) <= ${B}`);
      }), 'n');
      const ex = X.exI(X.tc(cM, [mem(cM, B, f), nn], `${B} in Real & all n. (n in Nat -> abs(a[n]) <= ${B})`), 'M', 'M in Real & all n. (n in Nat -> abs(a[n]) <= M)', B);
      return X.tc(cM, [X.inst(X.defAx('SeqBdd'), ['a']), sa, ex], 'SeqBdd(a)');
    }, cN);
  }, k);
}), 'a'));

prove('CauchyComplete', 'all a. (Cgt(a) <-> Cauchy(a))', '定理6.11', () => X.gen((() => {
  const fw = X.assume([], 'Cgt(a)', (h, k) => X.exE(X.tc(k, [h, X.inst(X.defAx('Cgt'), ['a'])], 'ex al. Conv(a,al)'), 'al', (ha, c) => {
    const sa = use('ConvSeq', ['a', 'al'], c, [ha]), ar = use('ConvR', ['a', 'al'], c, [ha]);
    const all = X.gen(X.assume(c, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => {
      const e = 'eps * 2^-1';
      return X.exE(use('Tail', ['a', 'al', 'a', 'al', e], c2, [ha, ha, mem(c2, e, [he]), use('HalfPos', ['eps'], c2, [he, hp])]), 'N', (hN, cN) => {
        const nN = X.tc(cN, [hN], 'N in Nat');
        const tl = X.tc(cN, [hN], `all n. (n in Nat -> N <= n -> abs(a[n] - al) < ${e} & abs(a[n] - al) < ${e})`);
        const body = X.gen(X.gen(X.assume(cN, 'm in Nat', (hm, c3) => X.assume(c3, 'n in Nat', (hn, c4) => X.assume(c4, 'N <= m', (hl1, c5) => X.assume(c5, 'N <= n', (hl2, c6) => {
          const g = [sa, hm, hn, ar, he];
          const am = X.tc(c6, [X.inst(tl, ['m']), hm, hl1], `abs(a[m] - al) < ${e}`);
          const an = X.tc(c6, [X.inst(tl, ['n']), hn, hl2], `abs(a[n] - al) < ${e}`);
          const am2 = X.rw(use('AbsSubComm', ['a[m]', 'al'], c6, g), am, `abs(al - a[m]) < ${e}`, c6);
          const r = use('ErrTwo', ['al', 'a[m]', 'a[n]', e], c6, [...g, mem(c6, e, g), am2, X.rw(use('AbsSubComm', ['a[n]', 'al'], c6, g), an, `abs(al - a[n]) < ${e}`, c6)]);
          return X.rw(use('HalfSum', ['eps'], c6, g), r, 'abs(a[m] - a[n]) < eps', c6);
        })))), 'n'), 'm');
        const G = 'N in Nat & all m. all n. (m in Nat -> n in Nat -> N <= m -> N <= n -> abs(a[m] - a[n]) < eps)';
        return X.exI(X.tc(cN, [nN, body], G), 'N', G, 'N');
      });
    })), 'eps');
    return X.tc(c, [X.inst(X.defAx('Cauchy'), ['a']), sa, all], 'Cauchy(a)');
  }, k));
  const bw = X.assume([], 'Cauchy(a)', (h, k) => {
    const sa = X.tc(k, [h, X.inst(X.defAx('Cauchy'), ['a'])], 'Seq(a)');
    return X.exE(use('BW', ['a'], k, [use('CauchyBdd', ['a'], k, [h])]), 'b', (hb, cb) => {
      const sub = X.tc(cb, [hb, X.inst(X.defAx('SubSeq'), ['b', 'a'])], 'Seq(b) & ex s. (SubIdx(s) & all k. (k in Nat -> b[k] = a[s[k]]))');
      return X.exE(X.tc(cb, [hb, X.inst(X.defAx('Cgt'), ['b'])], 'ex al. Conv(b,al)'), 'c', (hc, cc) => X.exE(X.tc(cc, [sub], 'ex s. (SubIdx(s) & all k. (k in Nat -> b[k] = a[s[k]]))'), 's', (hs, cs) => {
        const si = X.tc(cs, [hs], 'SubIdx(s)');
        const ns = X.tc(cs, [si, X.inst(X.defAx('SubIdx'), ['s'])], 'NSeq(s)');
        const cr = use('ConvR', ['b', 'c'], cs, [hc]), sb = use('ConvSeq', ['b', 'c'], cs, [hc]);
        const ge = use('IdxGe', ['s'], cs, [si]);
        const conv = convIntro(cs, 'a', 'c', sa, cr, (c2, he, hp) => {
          const e = 'eps * 2^-1';
          const ep = use('HalfPos', ['eps'], c2, [he, hp]), er = mem(c2, e, [he]);
          return X.exE(use('CauchyE', ['a', e], c2, [h, er, ep]), 'N1', (h1, d1) => X.exE(use('ConvE', ['b', 'c', e], d1, [hc, er, ep]), 'N2', (h2, d) => {
            const n1 = X.tc(d, [h1], 'N1 in Nat'), n2 = X.tc(d, [h2], 'N2 in Nat');
            const cq = X.tc(d, [h1], `all m. all n. (m in Nat -> n in Nat -> N1 <= m -> N1 <= n -> abs(a[m] - a[n]) < ${e})`);
            return tailIntro(d, 'N1', n1, n => `abs(a[${n}] - c) < eps`, (cl, hn, hl) => {
              const kk = 'cup(N1, N2)';
              const kn = use('NatCup', ['N1', 'N2'], cl, [n1, n2]);
              const sk = use('NSeqVal', ['s', kk], cl, [ns, kn]);
              const g = [sa, sb, hn, sk, kn, cr, er];
              const k1 = use('LeTrans', ['N1', kk, `s[${kk}]`], cl, [X.inst(X.thm('LeCupL'), ['N1', 'N2']), X.tc(cl, [X.inst(ge, [kk]), kn], `${kk} <= s[${kk}]`)]);
              const d1l = X.tc(cl, [X.inst(cq, ['n', `s[${kk}]`]), hn, sk, hl, k1], `abs(a[n] - a[s[${kk}]]) < ${e}`);
              const d2l = tailAt(cl, h2, 'N2', n => `abs(b[${n}] - c) < ${e}`, kk, kn, X.inst(X.thm('LeCupR'), ['N1', 'N2']));
              const d2 = X.rw(X.tc(cl, [X.inst(X.tc(cl, [hs], 'all k. (k in Nat -> b[k] = a[s[k]])'), [kk]), kn], `b[${kk}] = a[s[${kk}]]`), d2l, `abs(a[s[${kk}]] - c) < ${e}`, cl);
              const r = use('ErrChain', ['a[n]', `a[s[${kk}]]`, 'c', e], cl, [...g, d1l, d2]);
              return X.rw(use('HalfSum', ['eps'], cl, g), r, 'abs(a[n] - c) < eps', cl);
            });
          }, d1));
        });
        return X.tc(cs, [X.inst(X.defAx('Cgt'), ['a']), X.exI(conv, 'al', 'Conv(a,al)', 'c')], 'Cgt(a)');
      }, cc), cb);
    }, k);
  });
  return X.tc([], [fw, bw], 'Cgt(a) <-> Cauchy(a)');
})(), 'a'));

module.exports = {};
