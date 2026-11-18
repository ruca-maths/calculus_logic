'use strict';
// テキスト第3章 2節(続き): 有界性, 積・商の極限, 絶対値, ∞ への発散, 部分列
const K = require('./kit');
const { X, C, prove, intro, use, calc, mem, P } = K;
const { def, fthm } = require('./theory');
const L = require('./lang');
const { indNat, monoThm } = require('./p_nat');
require('./p_more');

// ---------------- 記号と基礎定理 ----------------
L.defFunc('cseq', 1, a => `\\overline{${a[0]}}`);
L.defFunc('absq', 1, a => `\\lvert ${a[0]} \\rvert`);
L.defFunc('sseq', 2, a => `${a[0]} \\circ ${a[1]}`, 50);
L.defFunc('ran', 1, a => `\\mathrm{ran}(${a[0]})`);
L.defFunc('sucf', 0, () => '\\mathsf{s}');
L.defFunc('evn', 0, () => '\\mathsf{e}');
L.defFunc('odn', 0, () => '\\mathsf{o}');
L.defPred('NSeq', 1, a => `\\mathrm{NSeq}(${a[0]})`);
L.defPred('SubIdx', 1, a => `\\mathrm{SubIdx}(${a[0]})`);

fthm('ConstSeq', 'all c. (c in Real -> Seq(cseq(c)) & all n. (n in Nat -> cseq(c)[n] = c))', '[S10]', '定義 (x∈A↦t)');
fthm('AbsSeq', 'all a. (Seq(a) -> Seq(absq(a)) & all n. (n in Nat -> absq(a)[n] = abs(a[n])))', '[S11]', '定義 (x∈A↦t)');
fthm('SubSeqF', 'all a. all s. (Seq(a) -> NSeq(s) -> Seq(sseq(a,s)) & all k. (k in Nat -> sseq(a,s)[k] = a[s[k]]))', '[S12]', '関数の合成');
fthm('NSeqVal', 'all s. all k. (NSeq(s) -> k in Nat -> s[k] in Nat)', '[S13]', '補題(関数値)');
fthm('Sucf', 'NSeq(sucf) & all k. (k in Nat -> sucf[k] = S(k))', '[S14]', '定義 (x∈A↦t)');
fthm('EvOd', 'NSeq(evn) & NSeq(odn) & (all k. (k in Nat -> evn[k] < evn[S(k)] & odn[k] < odn[S(k)])) & (all n. (n in Nat -> ex k. (k in Nat & (n = evn[k] | n = odn[k]))))', '[S15]', '定理(ωの演算)');
fthm('LtS', 'all n. (n in omega -> n < S(n))', '[N17]', '定理(ωの順序)');

def('SubIdx', 'all s. (SubIdx(s) <-> NSeq(s) & all k. (k in Nat -> s[k] < s[S(k)]))', 'DefSubIdx');
def('SubSeq', 'all b. all a. (SubSeq(b,a) <-> Seq(b) & ex s. (SubIdx(s) & all k. (k in Nat -> b[k] = a[s[k]])))', 'DefSubSeq');

// ---------------- 補助手続き ----------------
const convDef = (a, al) => X.inst(X.defAx('Conv'), [a, al]);
function convIntro(c, a, al, seqLine, alR, bodyFn) {
  const all = X.gen(X.assume(c, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => bodyFn(c2, he, hp))), 'eps');
  return X.tc(c, [convDef(a, al), seqLine, alR, all], `Conv(${a}, ${al})`);
}
// c ⊢ ∃N (N∈ℕ ∧ ∀n (n∈ℕ → N ≤ n → goal(n)))  (証拠 Nt, body(cl, hn, hl) : cl ⊢ goal('n'))
function tailIntro(c, Nt, nNat, goal, body) {
  const b = X.assume(c, 'n in Nat', (hn, cn) => X.assume(cn, `${Nt} <= n`, (hl, cl) => body(cl, hn, hl)));
  const G = N => `${N} in Nat & all n. (n in Nat -> ${N} <= n -> ${goal('n')})`;
  return X.exI(X.tc(c, [nNat, X.gen(b, 'n')], G(Nt)), 'N', G('N'), Nt);
}
// ∃N (...) の行から N をとり出し, ∀n の部分を n で例化する補助
const tailAt = (c, hN, N, goal, n, hn, hl) => X.tc(c, [X.inst(X.tc(c, [hN], `all n. (n in Nat -> ${N} <= n -> ${goal('n')})`), [n]), hn, hl], goal(n));
const seqParts = (c, name, args, facts) => { const l = use(name, args, c, facts); return l; };

// ---------------- 収束は値だけで決まる ----------------
prove('ConvExt', 'all a. all b. all al. (Seq(b) -> (all n. (n in Nat -> a[n] = b[n])) -> Conv(a,al) -> Conv(b,al))', '[C13]', () => X.genAll(
  X.assume([], 'Seq(b)', (hb, k1) => X.assume(k1, 'all n. (n in Nat -> a[n] = b[n])', (he, k2) => X.assume(k2, 'Conv(a,al)', (ha, k) => {
    const ar = use('ConvR', ['a', 'al'], k, [ha]);
    return convIntro(k, 'b', 'al', hb, ar, (c2, he2, hp) => X.exE(use('ConvE', ['a', 'al', 'eps'], c2, [ha, he2, hp]), 'N', (hN, cN) =>
      tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `abs(b[${n}] - al) < eps`, (cl, hn, hl) => {
        const l = tailAt(cl, hN, 'N', n => `abs(a[${n}] - al) < eps`, 'n', hn, hl);
        return X.rw(X.tc(cl, [X.inst(he, ['n']), hn], 'a[n] = b[n]'), l, 'abs(b[n] - al) < eps', cl);
      })));
  }))), ['a', 'b', 'al']));

// ---------------- 有限個の項の上界 ----------------
prove('FinBound', 'all a. (Seq(a) -> all N. (N in Nat -> ex M. (M in Real & 0 <= M & all n. (n in Nat -> n <= N -> abs(a[n]) <= M))))', '[C14]', () => X.gen(
  X.assume([], 'Seq(a)', (sa, c0) => {
    const G = (N, M) => `${M} in Real & 0 <= ${M} & all n. (n in Nat -> n <= ${N} -> abs(a[n]) <= ${M})`;
    const one = X.thm('NatOne');
    const a1 = 'abs(a[onew])';
    const base = (() => {
      const r = mem(c0, a1, [sa, one]);
      const nn = X.gen(X.assume(c0, 'n in Nat', (hn, c1) => X.assume(c1, 'n <= onew', (hl, c2) => {
        const e = use('LeAntisym', ['n', 'onew'], c2, [hl, use('OneLe', ['n'], c2, [hn])]);
        return X.rw(e, X.tc(c2, [X.refl('abs(a[n])')], 'abs(a[n]) <= abs(a[n])'), `abs(a[n]) <= ${a1}`, c2);
      })), 'n');
      return X.exI(X.tc(c0, [r, use('AbsNonneg', ['a[onew]'], c0, [sa, one]), nn], G('onew', a1)), 'M', G('onew', 'M'), a1);
    })();
    return indNat(c0, 'N', `ex M. (${G('N', 'M')})`, base, (c, N, hN, hp) => X.exE(hp, 'M', (hM, cM) => {
      const mr = X.tc(cM, [hM], 'M in Real'), m0 = X.tc(cM, [hM], '0 <= M');
      const sN = use('NatS', ['N'], cM, [hN]);
      const t = 'abs(a[S(N)])', M2 = `M + ${t}`;
      const f = [sa, sN, mr];
      const tn = use('AbsNonneg', ['a[S(N)]'], cM, f);
      const nn = X.gen(X.assume(cM, 'n in Nat', (hn, c1) => X.assume(c1, 'n <= S(N)', (hl, c2) => {
        const cs = use('LeSCases', ['n', 'N'], c2, [use('NatOmega', ['n'], c2, [hn]), use('NatOmega', ['N'], c2, [hN]), hl]);
        const l1 = X.assume(c2, 'n <= N', (h1, c3) => {
          const b = X.tc(c3, [X.inst(X.tc(c3, [hM], 'all n. (n in Nat -> n <= N -> abs(a[n]) <= M)'), ['n']), hn, h1], 'abs(a[n]) <= M');
          return use('LeTrans', ['abs(a[n])', 'M', M2], c3, [b, use('LeAddNonneg', ['M', t], c3, [...f, tn])]);
        });
        const l2 = X.assume(c2, 'n = S(N)', (h1, c3) => X.rw(X.sym(h1), use('LeAddNonnegL', [t, 'M'], c3, [...f, m0]), `abs(a[n]) <= ${M2}`, c3));
        return X.tc(c2, [cs, l1, l2], `abs(a[n]) <= ${M2}`);
      })), 'n');
      const w = X.tc(cM, [mem(cM, M2, f), use('AddNonnegNonneg', ['M', t], cM, [...f, m0, tn]), nn], G('S(N)', M2));
      return X.exI(w, 'M', G('S(N)', 'M'), M2);
    }));
  }), 'a'));

// ---------------- 定理 2.11: 収束列の有界性 ----------------
prove('ConvBdd', 'all a. all al. (Conv(a,al) -> SeqBdd(a))', '定理2.11', () => X.genAll(X.assume([], 'Conv(a,al)', (ha, k) => {
  const sa = use('ConvSeq', ['a', 'al'], k, [ha]), ar = use('ConvR', ['a', 'al'], k, [ha]);
  const one = X.tc(k, [X.thm('ZeroLtOne')], '0 < 1');
  return X.exE(use('ConvE', ['a', 'al', '1'], k, [ha, X.thm('R1_1'), one]), 'N', (hN, cN) => {
    const nN = X.tc(cN, [hN], 'N in Nat');
    return X.exE(X.tc(cN, [X.inst(use('FinBound', ['a'], cN, [sa]), ['N']), nN], 'ex M. (M in Real & 0 <= M & all n. (n in Nat -> n <= N -> abs(a[n]) <= M))'), 'M', (hM, cM) => {
      const mr = X.tc(cM, [hM], 'M in Real'), m0 = X.tc(cM, [hM], '0 <= M');
      const A = '1 + abs(al)', B = `M + (${A})`;
      const f = [sa, ar, mr];
      const a0 = use('AddNonnegNonneg', ['1', 'abs(al)'], cM, [...f, X.tc(cM, [one], '0 <= 1'), use('AbsNonneg', ['al'], cM, f)]);
      const nn = X.gen(X.assume(cM, 'n in Nat', (hn, c1) => {
        const g = [...f, hn];
        const cs = use('OmegaTotal', ['N', 'n'], c1, [use('NatOmega', ['N'], c1, [nN]), use('NatOmega', ['n'], c1, [hn])]);
        const big = X.assume(c1, 'N <= n', (hl, c2) => {
          const d = X.tc(c2, [X.inst(X.tc(c2, [hN], 'all n. (n in Nat -> N <= n -> abs(a[n] - al) < 1)'), ['n']), hn, hl], 'abs(a[n] - al) < 1');
          const t = X.rw(use('SubAdd', ['a[n]', 'al'], c2, g), use('Triangle', ['a[n] - al', 'al'], c2, g), 'abs(a[n]) <= abs(a[n] - al) + abs(al)', c2);
          const s = use('AddLtLe', ['abs(a[n] - al)', '1', 'abs(al)', 'abs(al)'], c2, [...g, d, X.tc(c2, [X.refl('abs(al)')], 'abs(al) <= abs(al)')]);
          const l = X.tc(c2, [use('LeLtTrans', ['abs(a[n])', 'abs(a[n] - al) + abs(al)', A], c2, [...g, t, s])], `abs(a[n]) <= ${A}`);
          return use('LeTrans', ['abs(a[n])', A, B], c2, [l, use('LeAddNonnegL', [A, 'M'], c2, [...g, m0])]);
        });
        const small = X.assume(c1, 'n < N', (hl, c2) => {
          const b = X.tc(c2, [X.inst(X.tc(c2, [hM], 'all n. (n in Nat -> n <= N -> abs(a[n]) <= M)'), ['n']), hn, hl], 'abs(a[n]) <= M');
          return use('LeTrans', ['abs(a[n])', 'M', B], c2, [b, use('LeAddNonneg', ['M', A], c2, [...g, a0])]);
        });
        return X.tc(c1, [cs, big, small], `abs(a[n]) <= ${B}`);
      }), 'n');
      const w = X.tc(cM, [mem(cM, B, f), nn], `${B} in Real & all n. (n in Nat -> abs(a[n]) <= ${B})`);
      const ex = X.exI(w, 'M', 'M in Real & all n. (n in Nat -> abs(a[n]) <= M)', B);
      return X.tc(cM, [X.inst(X.defAx('SeqBdd'), ['a']), sa, ex], 'SeqBdd(a)');
    }, cN);
  }, k);
}), ['a', 'al']));

// ---------------- 定理 2.7: 積の極限 ----------------
prove('ErrProd', 'all x. all y. all al. all be. all M. all h. (x in Real -> y in Real -> al in Real -> be in Real -> M in Real -> h in Real -> 0 <= M -> abs(x) <= M -> abs(x - al) < h -> abs(y - be) < h -> abs(x * y - al * be) <= (M + abs(be)) * h)', '[C15]', () =>
  intro(['x', 'y', 'al', 'be', 'M', 'h'], ['0 <= M', 'abs(x) <= M', 'abs(x - al) < h', 'abs(y - be) < h'], (c, [m0, hx, h1, h2]) => {
    const e = use('MulSubSplit', ['x', 'y', 'al', 'be'], c);
    const t = X.rw(X.sym(e), use('Triangle', ['x * (y - be)', 'be * (x - al)'], c), 'abs(x * y - al * be) <= abs(x * (y - be)) + abs(be * (x - al))', c);
    const t1 = X.rw(use('AbsMul', ['be', 'x - al'], c), X.rw(use('AbsMul', ['x', 'y - be'], c), t, 'abs(x * y - al * be) <= abs(x) * abs(y - be) + abs(be * (x - al))', c),
      'abs(x * y - al * be) <= abs(x) * abs(y - be) + abs(be) * abs(x - al)', c);
    const p = use('MulLeLe', ['abs(x)', 'M', 'abs(y - be)', 'h'], c, [use('AbsNonneg', ['x'], c), use('AbsNonneg', ['y - be'], c), hx, X.tc(c, [h2], 'abs(y - be) <= h')]);
    const q = use('MulLeLe', ['abs(be)', 'abs(be)', 'abs(x - al)', 'h'], c, [use('AbsNonneg', ['be'], c), use('AbsNonneg', ['x - al'], c), X.tc(c, [X.refl('abs(be)')], 'abs(be) <= abs(be)'), X.tc(c, [h1], 'abs(x - al) <= h')]);
    const s = use('AddLeLe', ['abs(x) * abs(y - be)', 'M * h', 'abs(be) * abs(x - al)', 'abs(be) * h'], c, [p, q]);
    const d = calc(c, 'M * h + abs(be) * h', [['h * M + abs(be) * h', use('R7', ['M', 'h'], c)], ['h * M + h * abs(be)', use('R7', ['abs(be)', 'h'], c)],
      ['h * (M + abs(be))', X.sym(use('R10', ['h', 'M', 'abs(be)'], c))], ['(M + abs(be)) * h', use('R7', ['h', 'M + abs(be)'], c)]]);
    return use('LeTrans', ['abs(x * y - al * be)', 'abs(x) * abs(y - be) + abs(be) * abs(x - al)', '(M + abs(be)) * h'], c, [t1, X.rw(d, s, 'abs(x) * abs(y - be) + abs(be) * abs(x - al) <= (M + abs(be)) * h', c)]);
  }));

prove('LimProd', 'all a. all al. all b. all be. (Conv(a,al) -> Conv(b,be) -> Conv(otimes(a,b), al * be))', '定理2.7', () => X.genAll(
  X.assume([], 'Conv(a,al)', (ha, c1) => X.assume(c1, 'Conv(b,be)', (hb, k) => {
    const sa = use('ConvSeq', ['a', 'al'], k, [ha]), sb = use('ConvSeq', ['b', 'be'], k, [hb]);
    const ar = use('ConvR', ['a', 'al'], k, [ha]), br = use('ConvR', ['b', 'be'], k, [hb]);
    const ot = use('Otimes', ['a', 'b'], k, [sa, sb]);
    const bd = X.tc(k, [use('ConvBdd', ['a', 'al'], k, [ha]), X.inst(X.defAx('SeqBdd'), ['a'])], 'ex M. (M in Real & all n. (n in Nat -> abs(a[n]) <= M))');
    return X.exE(bd, 'M', (hM, cM) => {
      const mr = X.tc(cM, [hM], 'M in Real');
      const ball = X.tc(cM, [hM], 'all n. (n in Nat -> abs(a[n]) <= M)');
      const one = X.thm('NatOne');
      const m0 = use('LeTrans', ['0', 'abs(a[onew])', 'M'], cM, [use('AbsNonneg', ['a[onew]'], cM, [sa, one]), X.tc(cM, [X.inst(ball, ['onew']), one], 'abs(a[onew]) <= M')]);
      const f = [sa, sb, ar, br, mr];
      const Mb = 'M + abs(be)', Kt = `(${Mb}) + 1`;
      const mb0 = use('AddNonnegNonneg', ['M', 'abs(be)'], cM, [...f, m0, use('AbsNonneg', ['be'], cM, f)]);
      const kp = use('LeLtTrans', ['0', Mb, Kt], cM, [mb0, use('LtAddOne', [Mb], cM, f)]);
      const kn = X.neSym(use('LtNe', ['0', Kt], cM, [kp]));
      return convIntro(cM, 'otimes(a,b)', 'al * be', X.tc(cM, [ot], 'Seq(otimes(a,b))'), mem(cM, 'al * be', f), (c2, he, hp) => {
        const e2 = `(eps * (${Kt})^-1)`;
        const g = [...f, he, kn];
        const e2p = use('R15', ['eps', `(${Kt})^-1`], c2, [...g, hp, use('InvPos', [Kt], c2, [...g, kp])]);
        return X.exE(use('Tail', ['a', 'al', 'b', 'be', e2], c2, [ha, hb, mem(c2, e2, g), e2p]), 'N', (hN, cN) =>
          tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `abs(otimes(a,b)[${n}] - al * be) < eps`, (cl, hn, hl) => {
            const gg = [...g, hn];
            const both = tailAt(cl, hN, 'N', n => `abs(a[${n}] - al) < ${e2} & abs(b[${n}] - be) < ${e2}`, 'n', hn, hl);
            const ep = use('ErrProd', ['a[n]', 'b[n]', 'al', 'be', 'M', e2], cl, [...gg, m0, X.tc(cl, [X.inst(ball, ['n']), hn], 'abs(a[n]) <= M'),
              X.tc(cl, [both], `abs(a[n] - al) < ${e2}`), X.tc(cl, [both], `abs(b[n] - be) < ${e2}`)]);
            const lt = use('MulLtPos', [Mb, Kt, e2], cl, [...gg, e2p, use('LtAddOne', [Mb], cl, gg)]);
            const simp = calc(cl, `(${Kt}) * ${e2}`, [[`${e2} * (${Kt})`, use('R7', [Kt, e2], cl, gg)], ['eps', use('DivMul', ['eps', Kt], cl, gg)]]);
            const r = use('LeLtTrans', ['abs(a[n] * b[n] - al * be)', `(${Mb}) * ${e2}`, 'eps'], cl, [ep, X.rw(simp, lt, `(${Mb}) * ${e2} < eps`, cl)]);
            return X.rw(X.sym(X.tc(cl, [X.inst(X.tc(cl, [ot], 'all n. (n in Nat -> otimes(a,b)[n] = a[n] * b[n])'), ['n']), hn], 'otimes(a,b)[n] = a[n] * b[n]')), r, 'abs(otimes(a,b)[n] - al * be) < eps', cl);
          }));
      });
    }, k);
  })), ['a', 'al', 'b', 'be']));

// ---------------- 定理 2.9: 商の極限 ----------------
prove('LimRecip', 'all b. all be. (Conv(b,be) -> be != 0 -> (all n. (n in Nat -> b[n] != 0)) -> Conv(recip(b), be^-1))', '定理2.9(逆数)', () => X.genAll(
  X.assume([], 'Conv(b,be)', (hb, k1) => X.assume(k1, 'be != 0', (hz, k2) => X.assume(k2, 'all n. (n in Nat -> b[n] != 0)', (hnz, k) => {
    const sb = use('ConvSeq', ['b', 'be'], k, [hb]), br = use('ConvR', ['b', 'be'], k, [hb]);
    const rc = use('Recip', ['b'], k, [sb, hnz]);
    const f = [sb, br, hz];
    const d = 'abs(be) * 2^-1';
    const bp = use('AbsPos', ['be'], k, f);
    const dp = use('HalfPos', ['abs(be)'], k, [...f, bp]);
    const bn = X.neSym(use('LtNe', ['0', 'abs(be)'], k, [bp])), dn = X.neSym(use('LtNe', ['0', d], k, [dp]));
    const db = `${d} * abs(be)`;
    const dbp = use('R15', [d, 'abs(be)'], k, [...f, dp, bp]);
    return convIntro(k, 'recip(b)', 'be^-1', X.tc(k, [rc], 'Seq(recip(b))'), mem(k, 'be^-1', f), (c2, he, hp) => {
      const e1 = `(eps * (${db}))`;
      const g = [...f, he, bn, dn];
      const e1p = use('R15', ['eps', db], c2, [...g, hp, dbp]);
      return X.exE(use('MinPos', [d, e1], c2, [...g, mem(c2, e1, g), dp, e1p]), 'd0', (hd, cd) => {
        const d0r = X.tc(cd, [hd], 'd0 in Real'), d0p = X.tc(cd, [hd], '0 < d0');
        return X.exE(use('ConvE', ['b', 'be', 'd0'], cd, [hb, d0r, d0p]), 'N', (hN, cN) =>
          tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `abs(recip(b)[${n}] - be^-1) < eps`, (cl, hn, hl) => {
            const gg = [...g, hn, d0r];
            const bnz = X.tc(cl, [X.inst(hnz, ['n']), hn], 'b[n] != 0');
            const lt0 = tailAt(cl, hN, 'N', n => `abs(b[${n}] - be) < d0`, 'n', hn, hl);
            const ltd = use('LtLeTrans', ['abs(b[n] - be)', 'd0', d], cl, [lt0, X.tc(cl, [hd], `d0 <= ${d}`)]);
            const lte = use('LtLeTrans', ['abs(b[n] - be)', 'd0', e1], cl, [lt0, X.tc(cl, [hd], `d0 <= ${e1}`)]);
            const low = use('AbsLowerHalf', ['b[n]', 'be'], cl, [...gg, ltd]); // d < |b_n|
            const bnp = use('AbsPos', ['b[n]'], cl, [...gg, bnz]);
            const bnn = X.neSym(use('LtNe', ['0', 'abs(b[n])'], cl, [bnp]));
            // |b_n^{-1} - β^{-1}| = |β - b_n| · (|b_n|^{-1} |β|^{-1})
            const w = '(abs(b[n])^-1 * abs(be)^-1)';
            const ggg = [...gg, bnz, bnn];
            const eq = calc(cl, 'abs(b[n]^-1 - be^-1)', [
              ['abs((be - b[n]) * (b[n]^-1 * be^-1))', use('SubInv', ['b[n]', 'be'], cl, ggg)],
              ['abs(be - b[n]) * abs(b[n]^-1 * be^-1)', use('AbsMul', ['be - b[n]', 'b[n]^-1 * be^-1'], cl, ggg)],
              ['abs(be - b[n]) * (abs(b[n]^-1) * abs(be^-1))', use('AbsMul', ['b[n]^-1', 'be^-1'], cl, ggg)],
              [`abs(be - b[n]) * (abs(b[n])^-1 * abs(be^-1))`, use('AbsInv', ['b[n]'], cl, ggg)],
              [`abs(be - b[n]) * ${w}`, use('AbsInv', ['be'], cl, ggg)],
              [`abs(b[n] - be) * ${w}`, use('AbsSubComm', ['be', 'b[n]'], cl, ggg)]]);
            const wp = use('R15', ['abs(b[n])^-1', 'abs(be)^-1'], cl, [...ggg, use('InvPos', ['abs(b[n])'], cl, [...ggg, bnp]), use('InvPos', ['abs(be)'], cl, [...ggg, bp])]);
            const s1 = use('MulLtPos', ['abs(b[n] - be)', e1, w], cl, [...ggg, wp, lte]);   // |..| w < e1 w
            // w < d^{-1} |β|^{-1}
            const il = use('InvLt', [d, 'abs(b[n])'], cl, [...ggg, dp, low]);
            const w2 = use('MulLtPos', ['abs(b[n])^-1', `(${d})^-1`, 'abs(be)^-1'], cl, [...ggg, use('InvPos', ['abs(be)'], cl, [...ggg, bp]), il]);
            const s2 = use('MulLtPosL', [w, `((${d})^-1 * abs(be)^-1)`, e1], cl, [...ggg, e1p, w2]);
            const simp = calc(cl, `${e1} * ((${d})^-1 * abs(be)^-1)`, [
              [`${e1} * (${db})^-1`, X.sym(use('InvMul', [d, 'abs(be)'], cl, ggg))],
              ['eps * ((' + db + ') * (' + db + ')^-1)', use('R6', ['eps', db, `(${db})^-1`], cl, [...ggg, X.neSym(use('LtNe', ['0', db], cl, [dbp]))])],
              ['eps * 1', use('R9', [db], cl, [...ggg, X.neSym(use('LtNe', ['0', db], cl, [dbp]))])],
              ['eps', use('R8', ['eps'], cl, ggg)]]);
            const s3 = use('LtTrans', [`abs(b[n] - be) * ${w}`, `${e1} * ${w}`, 'eps'], cl, [s1, X.rw(simp, s2, `${e1} * ${w} < eps`, cl)]);
            const r = X.rw(X.sym(eq), s3, 'abs(b[n]^-1 - be^-1) < eps', cl);
            return X.rw(X.sym(X.tc(cl, [X.inst(X.tc(cl, [rc], 'all n. (n in Nat -> recip(b)[n] = b[n]^-1)'), ['n']), hn], 'recip(b)[n] = b[n]^-1')), r, 'abs(recip(b)[n] - be^-1) < eps', cl);
          }));
      }, c2);
    });
  }))), ['b', 'be']));
prove('LimQuot', 'all a. all al. all b. all be. (Conv(a,al) -> Conv(b,be) -> be != 0 -> (all n. (n in Nat -> b[n] != 0)) -> Conv(otimes(a,recip(b)), al * be^-1))', '定理2.9', () => X.genAll(
  X.assume([], 'Conv(a,al)', (ha, k1) => X.assume(k1, 'Conv(b,be)', (hb, k2) => X.assume(k2, 'be != 0', (hz, k3) => X.assume(k3, 'all n. (n in Nat -> b[n] != 0)', (hnz, k) =>
    use('LimProd', ['a', 'al', 'recip(b)', 'be^-1'], k, [ha, use('LimRecip', ['b', 'be'], k, [hb, hz, hnz])]))))), ['a', 'al', 'b', 'be']));

module.exports = { convIntro, tailIntro, tailAt, convDef };
