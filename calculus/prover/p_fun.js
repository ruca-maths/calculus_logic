'use strict';
// テキスト第4章 1節(続き): 関数の極限と数列の極限(定理1.7 ⇐), 極限の性質(定理1.8, 1.9), Cauchy の判定法(1.13), 片側極限
const K = require('./kit');
const { X, C, prove, intro, use, calc, mem, P, T } = K;
const { def, fthm } = require('./theory');
const L = require('./lang');
const { convIntro, tailIntro, tailAt } = require('./p_seq');
require('./p_seq4');

// ---------------- 記号 ----------------
L.defFunc('fadd', 2, a => `(${a[0]} + ${a[1]})`);
L.defFunc('fmul', 2, a => `(${a[0]} \\cdot ${a[1]})`);
L.defFunc('fscal', 2, a => `(${a[0]} ${a[1]})`);
L.defFunc('fdiv', 2, a => `(${a[0]} / ${a[1]})`);
L.defFunc('fabs', 1, a => `\\lvert ${a[0]} \\rvert`);
L.defFunc('apseq', 2, a => `\\pi_{${a[0]},${a[1]}}`);
for (const [n, ar] of [['RNbhd', 2], ['LNbhd', 2]]) L.defPred(n, ar, a => `\\mathrm{${n}}(${a.join(',')})`);

const fdom = (F, cond) => `all x. (x in dom(${F}) <-> ${cond})`;
const fval = (F, v) => `all x. (x in dom(${F}) -> ${F}[x] = ${v})`;
fthm('FAdd', `all f. all g. (RFn(f) -> RFn(g) -> RFn(fadd(f,g)) & (${fdom('fadd(f,g)', 'x in dom(f) & x in dom(g)')}) & (${fval('fadd(f,g)', 'f[x] + g[x]')}))`, '[S17]', '関数の和');
fthm('FMul', `all f. all g. (RFn(f) -> RFn(g) -> RFn(fmul(f,g)) & (${fdom('fmul(f,g)', 'x in dom(f) & x in dom(g)')}) & (${fval('fmul(f,g)', 'f[x] * g[x]')}))`, '[S18]', '関数の積');
fthm('FScal', `all l. all f. (l in Real -> RFn(f) -> RFn(fscal(l,f)) & (${fdom('fscal(l,f)', 'x in dom(f)')}) & (${fval('fscal(l,f)', 'l * f[x]')}))`, '[S19]', '関数の定数倍');
fthm('FDiv', `all f. all g. (RFn(f) -> RFn(g) -> RFn(fdiv(f,g)) & (${fdom('fdiv(f,g)', 'x in dom(f) & x in dom(g) & g[x] != 0')}) & (${fval('fdiv(f,g)', 'f[x] * g[x]^-1')}))`, '[S20]', '関数の商');
fthm('FAbs', `all f. (RFn(f) -> RFn(fabs(f)) & (${fdom('fabs(f)', 'x in dom(f)')}) & (${fval('fabs(f)', 'abs(f[x])')}))`, '[S21]', '関数の絶対値');
fthm('ApSeq', 'all c. all r. (c in Real -> r in Real -> Seq(apseq(c,r)) & all n. (n in Nat -> apseq(c,r)[n] = c + r * (iota(n) + 1)^-1))', '[S22]', '定義 (x∈A↦t)');

// 可算選択の図式 [CC]: ∀k∈ℕ ∃x∈ℝ ψ(k,x) → ∃q (Seq(q) ∧ ∀k∈ℕ ψ(k,q_k))  (選択公理による. 通常の証明は本文)
let ccN = 0;
function ccInst(psiS) {
  const psi = P(psiS);
  const params = [...C.fv(psi)].filter(v => v !== 'k' && v !== 'x');
  let stmt = C.Imp(C.All('k', C.Imp(C.Rel('in', C.V('k'), C.F('Nat')), C.Ex('x', C.And(C.Rel('in', C.V('x'), C.F('Real')), psi)))),
    C.Ex('q', C.And(C.Rel('Seq', C.V('q')), C.All('k', C.Imp(C.Rel('in', C.V('k'), C.F('Nat')), C.subst(psi, 'x', C.F('app', C.V('q'), C.V('k'))))))));
  for (let i = params.length - 1; i >= 0; i--) stmt = C.All(params[i], stmt);
  const name = 'CC' + (++ccN);
  const { registry } = require('./theory');
  C.Theory.thms.set(name, { f: stmt, status: 'F', note: '可算選択' });
  registry.push({ kind: 'F', name, f: stmt, label: `[CC${ccN}]`, note: '図式[CC]の例' });
  require('./latex').leafLabel.set('Thm:' + name, `[CC${ccN}]`);
  return (ctx, facts) => use(name, params, ctx, facts);
}

// ---------------- 補題 ----------------
prove('AddSub', 'all x. all y. (x in Real -> y in Real -> (x + y) - y = x)', '[E38]', () => intro(['x', 'y'], [], c => calc(c, '(x + y) - y', [['(x + y) + -y', X.inst(X.defAx('minus'), ['x + y', 'y'])], ['x + (y + -y)', use('R2', ['x', 'y', '-y'], c)], ['x + 0', use('R5', ['y'], c)], ['x', use('R4', ['x'], c)]])));
prove('Inv1', '1^-1 = 1', '[E35]', () => X.sym(use('InvUnique', ['1', '1'], [], [X.thm('R1_1'), X.neSym(X.thm('R8b')), use('R8', ['1'], [])])));
prove('AbsSelf0', 'all x. (x in Real -> 0 < abs(x - x) -> x != x)', '[E36]', () => intro(['x'], ['0 < abs(x - x)'], (c, [h]) => X.raa(c, 'x != x', (hn, c2) => {
  const z = calc(c2, 'abs(x - x)', [['abs(0)', use('SubSelf', ['x'], c2)], ['0', use('AbsOfNonneg', ['0'], c2, [X.tc(c2, [X.refl('0')], '0 <= 0')])]]);
  return [X.rw(z, h, '0 < 0', c2), X.inst(X.thm('LtIrrefl'), ['0'])];
})));
// 0 < |y - c| → y ≠ c
prove('PosAbsNe', 'all y. all c. (y in Real -> c in Real -> 0 < abs(y - c) -> y != c)', '[E37]', () => intro(['y', 'c'], ['0 < abs(y - c)'], (cx, [h]) => X.raa(cx, 'y != c', (hn, c2) => {
  const e = X.tc(c2, [hn], 'y = c');
  const h2 = X.rw(e, h, '0 < abs(c - c)', c2);
  return [use('AbsSelf0', ['c'], c2, [h2]), X.refl('c')];
})));

// ---------------- 近似列: c に収束し, 除外近傍 (半径 r) に属する数列 ----------------
prove('ApproxSeq', 'all c. all r. (c in Real -> r in Real -> 0 < r -> ex a. (Seq(a) & Conv(a,c) & all n. (n in Nat -> 0 < abs(a[n] - c) & abs(a[n] - c) < r)))', '[H1]', () =>
  intro(['c', 'r'], ['0 < r'], (k, [hr]) => {
    const A = 'apseq(c,r)';
    const ap = use('ApSeq', ['c', 'r'], k);
    const sa = X.tc(k, [ap], `Seq(${A})`);
    const val = X.tc(k, [ap], `all n. (n in Nat -> ${A}[n] = c + r * (iota(n) + 1)^-1)`);
    // 各 n で a_n - c = r (ι(n)+1)^{-1} > 0
    const facts = (cl, hn) => {
      const ip = use('IotaPos', ['n'], cl, [hn]);
      const ir = mem(cl, 'iota(n)', [hn]);
      const one = X.tc(cl, [X.thm('ZeroLtOne')], '0 < 1');
      const wp = use('AddPosPos', ['iota(n)', '1'], cl, [ir, ip, one]);
      const wn = X.neSym(use('LtNe', ['0', 'iota(n) + 1'], cl, [wp]));
      const g = [hn, wn];
      const w = '(iota(n) + 1)^-1';
      const wpos = use('InvPos', ['iota(n) + 1'], cl, [...g, wp]);
      const d = `r * ${w}`;
      const dpos = use('R15', ['r', w], cl, [...g, hr, wpos]);
      const v = X.tc(cl, [X.inst(val, ['n']), hn], `${A}[n] = c + ${d}`);
      const diff = calc(cl, `${A}[n] - c`, [[`(c + ${d}) - c`, v], [`(${d} + c) - c`, use('R3', ['c', d], cl, g)], [d, use('AddSub', [d, 'c'], cl, g)]]);
      const ab = calc(cl, `abs(${A}[n] - c)`, [[`abs(${d})`, diff], [d, use('AbsOfNonneg', [d], cl, [X.tc(cl, [dpos], `0 <= ${d}`)])]]);
      return { ab, dpos, g, w, d, wp, ip, ir };
    };
    const near = X.gen(X.assume(k, 'n in Nat', (hn, cl) => {
      const { ab, dpos, g, w, d, wp, ir } = facts(cl, hn);
      // (ι(n)+1)^{-1} < 1
      const lt1 = X.rw(use('R3', ['1', 'iota(n)'], cl, g), use('LtAddPos', ['1', 'iota(n)'], cl, [...g, use('IotaPos', ['n'], cl, [hn])]), '1 < iota(n) + 1', cl);
      const il = X.rw(X.thm('Inv1'), use('InvLt', ['1', 'iota(n) + 1'], cl, [...g, X.tc(cl, [X.thm('ZeroLtOne')], '0 < 1'), lt1]), `${w} < 1`, cl);
      const m = X.rw(use('R8', ['r'], cl, g), use('MulLtPosL', [w, '1', 'r'], cl, [...g, hr, il]), `${d} < r`, cl);
      return X.tc(cl, [X.rw(X.sym(ab), dpos, `0 < abs(${A}[n] - c)`, cl), X.rw(X.sym(ab), m, `abs(${A}[n] - c) < r`, cl)], `0 < abs(${A}[n] - c) & abs(${A}[n] - c) < r`);
    }), 'n');
    const rn = X.neSym(use('LtNe', ['0', 'r'], k, [hr]));
    const conv = convIntro(k, A, 'c', sa, X.hyp(k, 'c in Real'), (c2, he, hp) => {
      const e2 = '(eps * r^-1)';
      const e2p = use('R15', ['eps', 'r^-1'], c2, [he, rn, hp, use('InvPos', ['r'], c2, [hr])]);
      return X.exE(use('ArchInv', [e2], c2, [mem(c2, e2, [he, rn]), e2p]), 'K', (hK, cK) => {
        const kn = X.tc(cK, [hK], 'K in Nat');
        return tailIntro(cK, 'K', kn, n => `abs(${A}[${n}] - c) < eps`, (cl, hn, hl) => {
          const { ab, g, w, d, wp, ip, ir } = facts(cl, hn);
          const gg = [...g, he, rn, kn];
          const l1 = use('InvLt', ['iota(n)', 'iota(n) + 1'], cl, [...gg, ir, ip, use('LtAddOne', ['iota(n)'], cl, [ir])]);   // w < ι(n)^{-1}
          const l2 = use('LtLeTrans', [w, 'iota(n)^-1', 'iota(K)^-1'], cl, [l1, use('IotaInvMono', ['K', 'n'], cl, [kn, hn, hl])]);
          const l3 = use('LtTrans', [w, 'iota(K)^-1', e2], cl, [l2, X.tc(cl, [hK], `iota(K)^-1 < ${e2}`)]);
          const iK = X.neSym(use('LtNe', ['0', 'iota(K)'], cl, [use('IotaPos', ['K'], cl, [kn])]));
          const l4 = use('MulLtPosL', [w, e2, 'r'], cl, [...gg, iK, hr, l3]);
          const s = calc(cl, `r * ${e2}`, [[`${e2} * r`, use('R7', ['r', e2], cl, gg)], ['eps', use('DivMul', ['eps', 'r'], cl, gg)]]);
          return X.rw(X.sym(ab), X.rw(s, l4, `${d} < eps`, cl), `abs(${A}[n] - c) < eps`, cl);
        });
      });
    });
    const G = q => `Seq(${q}) & Conv(${q},c) & all n. (n in Nat -> 0 < abs(${q}[n] - c) & abs(${q}[n] - c) < r)`;
    return X.exI(X.tc(k, [sa, conv, near], G(A)), 'a', G('a'), A);
  }));

// ---------------- 定理 1.7 (⇐) ----------------
const EPSf = (f, c, al, e) => `ex de. (de in Real & 0 < de & all x. (x in dom(${f}) -> 0 < abs(x - ${c}) -> abs(x - ${c}) < de -> abs(${f}[x] - ${al}) < ${e}))`;
const EPS = (f, c, al) => `all eps. (eps in Real -> 0 < eps -> ${EPSf(f, c, al, 'eps')})`;
const SEQH = (f, c, al) => `(all a. (Seq(a) -> Conv(a,${c}) -> (all n. (n in Nat -> a[n] in dom(${f}) & a[n] != ${c})) -> Conv(compseq(${f},a), ${al})))`;
const PSI = 'x in dom(f) & 0 < abs(x - c) & abs(x - c) < iota(k)^-1 & ~ abs(f[x] - al) < e0';
const cc17 = ccInst(PSI);
prove('SeqCritInv', `all f. all c. all al. (RFn(f) -> c in Real -> al in Real -> PNbhd(f,c) -> ${SEQH('f', 'c', 'al')} -> FLim(f,c,al))`, '定理1.7(⇐)', () => X.genAll(
  X.assume([], 'RFn(f)', (rf, k1) => X.assume(k1, 'c in Real', (cr, k2) => X.assume(k2, 'al in Real', (ar, k3) => X.assume(k3, 'PNbhd(f,c)', (pn, k4) => X.assume(k4, SEQH('f', 'c', 'al'), (H, k) => {
    const eps = X.raa(k, EPS('f', 'c', 'al'), (hn, c2) => [X.exE(X.notAllToEx(hn), 'e0', (he0, c3) => {
      const e0r = X.tc(c3, [he0], 'e0 in Real'), e0p = X.tc(c3, [he0], '0 < e0');
      const never = X.tc(c3, [he0], 'all de. ~(de in Real & 0 < de & all x. (x in dom(f) -> 0 < abs(x - c) -> abs(x - c) < de -> abs(f[x] - al) < e0))');
      const pre = X.gen(X.assume(c3, 'k in Nat', (hk, ck) => {
        const ip = use('IotaPos', ['k'], ck, [hk]);
        const kz = X.neSym(use('LtNe', ['0', 'iota(k)'], ck, [ip]));
        const d = 'iota(k)^-1';
        const na = X.tc(ck, [X.inst(never, [d]), mem(ck, d, [hk, kz]), use('InvPos', ['iota(k)'], ck, [hk, ip])], `~ all x. (x in dom(f) -> 0 < abs(x - c) -> abs(x - c) < ${d} -> abs(f[x] - al) < e0)`);
        return X.exE(X.notAllToEx(na), 'x', (hx, cx) => {
          const xd = X.tc(cx, [hx], 'x in dom(f)');
          return X.exI(X.tc(cx, [hx, use('RFnDom', ['f', 'x'], cx, [rf, xd])], `x in Real & (${PSI})`), 'x', `x in Real & (${PSI})`, 'x');
        }, ck);
      }), 'k');
      return X.exE(cc17(c3, [pre]), 'a', (ha, ca) => {
        const sa = X.tc(ca, [ha], 'Seq(a)');
        const pa = X.tc(ca, [ha], `all k. (k in Nat -> ${PSI.replace(/\bx\b/g, 'a[k]')})`);
        const at = (cc, n, hn) => X.tc(cc, [X.inst(pa, [n]), hn], PSI.replace(/\bx\b/g, `a[${n}]`).replace(/\bk\b/g, n));
        const conv = convIntro(ca, 'a', 'c', sa, cr, (c4, he, hp) => X.exE(use('ArchInv', ['eps'], c4, [he, hp]), 'K', (hK, cK) => {
          const kn = X.tc(cK, [hK], 'K in Nat');
          return tailIntro(cK, 'K', kn, n => `abs(a[${n}] - c) < eps`, (cl, hn, hl) => {
            const p = at(cl, 'n', hn);
            const l = use('LtLeTrans', ['abs(a[n] - c)', 'iota(n)^-1', 'iota(K)^-1'], cl, [X.tc(cl, [p], 'abs(a[n] - c) < iota(n)^-1'), use('IotaInvMono', ['K', 'n'], cl, [kn, hn, hl])]);
            return use('LtTrans', ['abs(a[n] - c)', 'iota(K)^-1', 'eps'], cl, [l, X.tc(cl, [hK], 'iota(K)^-1 < eps')]);
          });
        }));
        const dom = X.gen(X.assume(ca, 'n in Nat', (hn, cn) => {
          const p = at(cn, 'n', hn);
          const ne = use('PosAbsNe', ['a[n]', 'c'], cn, [sa, hn, cr, X.tc(cn, [p], '0 < abs(a[n] - c)')]);
          return X.tc(cn, [p, ne], 'a[n] in dom(f) & a[n] != c');
        }), 'n');
        const dom1 = X.gen(X.assume(ca, 'n in Nat', (hn, cn) => X.tc(cn, [X.inst(dom, ['n']), hn], 'a[n] in dom(f)')), 'n');
        const fc = X.tc(ca, [X.inst(H, ['a']), sa, conv, dom], 'Conv(compseq(f,a), al)');
        const cs = use('CompSeq', ['f', 'a'], ca, [rf, sa, dom1]);
        return X.exE(use('ConvE', ['compseq(f,a)', 'al', 'e0'], ca, [fc, e0r, e0p]), 'N', (hN, cN) => {
          const nN = X.tc(cN, [hN], 'N in Nat');
          const l = tailAt(cN, hN, 'N', n => `abs(compseq(f,a)[${n}] - al) < e0`, 'N', nN, X.tc(cN, [X.refl('N')], 'N <= N'));
          const v = X.tc(cN, [X.inst(X.tc(cN, [cs], 'all n. (n in Nat -> compseq(f,a)[n] = f[a[n]])'), ['N']), nN], 'compseq(f,a)[N] = f[a[N]]');
          const l2 = X.rw(v, l, 'abs(f[a[N]] - al) < e0', cN);
          return X.tc(cN, [l2, at(cN, 'N', nN)], '0 < 0');
        }, ca);
      }, c3);
    }, c2), X.inst(X.thm('LtIrrefl'), ['0'])]);
    return X.tc(k, [X.inst(X.defAx('FLim'), ['f', 'c', 'al']), rf, cr, ar, pn, eps], 'FLim(f,c,al)');
  }))))), ['f', 'c', 'al']));

// ---------------- 定理 1.7 (同値形) ----------------
prove('FLimSeq', `all f. all c. all al. (FLim(f,c,al) <-> RFn(f) & c in Real & al in Real & PNbhd(f,c) & ${SEQH('f', 'c', 'al')})`, '定理1.7', () => X.genAll((() => {
  const fw = X.assume([], 'FLim(f,c,al)', (h, k) => {
    const sq = X.gen(X.assume(k, 'Seq(a)', (sa, c1) => X.assume(c1, 'Conv(a,c)', (ha, c2) => X.assume(c2, 'all n. (n in Nat -> a[n] in dom(f) & a[n] != c)', (hd, c3) =>
      use('SeqCrit', ['f', 'c', 'al', 'a'], c3, [h, ha, hd])))), 'a');
    return X.tc(k, [h, X.inst(X.defAx('FLim'), ['f', 'c', 'al']), sq], `RFn(f) & c in Real & al in Real & PNbhd(f,c) & ${SEQH('f', 'c', 'al')}`);
  });
  const bw = X.assume([], `RFn(f) & c in Real & al in Real & PNbhd(f,c) & ${SEQH('f', 'c', 'al')}`, (h, k) =>
    use('SeqCritInv', ['f', 'c', 'al'], k, ['RFn(f)', 'c in Real', 'al in Real', 'PNbhd(f,c)', SEQH('f', 'c', 'al')].map(s => X.tc(k, [h], s))));
  return X.tc([], [fw, bw], `FLim(f,c,al) <-> RFn(f) & c in Real & al in Real & PNbhd(f,c) & ${SEQH('f', 'c', 'al')}`);
})(), ['f', 'c', 'al']));

// 2つの除外近傍の共通部分
const PN = (f, c) => X.inst(X.defAx('PNbhd'), [f, c]);
const NB = (c, r, cond) => `all x. (x in Real -> 0 < abs(x - ${c}) -> abs(x - ${c}) < ${r} -> ${cond})`;
prove('PNbhdInter', `all f. all g. all c. (PNbhd(f,c) -> PNbhd(g,c) -> ex d. (d in Real & 0 < d & ${NB('c', 'd', 'x in dom(f) & x in dom(g)')}))`, '[H2]', () => X.genAll(
  X.assume([], 'PNbhd(f,c)', (h1, k1) => X.assume(k1, 'PNbhd(g,c)', (h2, k) =>
    X.exE(X.tc(k, [h1, PN('f', 'c')], `ex r. (r in Real & 0 < r & ${NB('c', 'r', 'x in dom(f)')})`), 'r1', (q1, d1) =>
      X.exE(X.tc(d1, [h2, PN('g', 'c')], `ex r. (r in Real & 0 < r & ${NB('c', 'r', 'x in dom(g)')})`), 'r2', (q2, d2) => {
        const r1 = X.tc(d2, [q1], 'r1 in Real'), r2 = X.tc(d2, [q2], 'r2 in Real');
        return X.exE(use('MinPos', ['r1', 'r2'], d2, [r1, r2, X.tc(d2, [q1], '0 < r1'), X.tc(d2, [q2], '0 < r2')]), 'd', (hd, cd) => {
          const all = X.gen(X.assume(cd, 'x in Real', (hx, c1) => X.assume(c1, '0 < abs(x - c)', (hp, c2) => X.assume(c2, 'abs(x - c) < d', (hl, c3) => {
            const a = X.tc(c3, [X.inst(X.tc(c3, [q1], NB('c', 'r1', 'x in dom(f)')), ['x']), hx, hp, use('LtLeTrans', ['abs(x - c)', 'd', 'r1'], c3, [hl, X.tc(c3, [hd], 'd <= r1')])], 'x in dom(f)');
            const b = X.tc(c3, [X.inst(X.tc(c3, [q2], NB('c', 'r2', 'x in dom(g)')), ['x']), hx, hp, use('LtLeTrans', ['abs(x - c)', 'd', 'r2'], c3, [hl, X.tc(c3, [hd], 'd <= r2')])], 'x in dom(g)');
            return X.tc(c3, [a, b], 'x in dom(f) & x in dom(g)');
          }))), 'x');
          const G = d => `${d} in Real & 0 < ${d} & ${NB('c', d, 'x in dom(f) & x in dom(g)')}`;
          return X.exI(X.tc(cd, [hd, all], G('d')), 'd', G('d'), 'd');
        }, d2);
      }, d1), k))), ['f', 'g', 'c']));

// 関数の演算に対する極限: 数列の極限に帰着する (定理1.7)
//   F の定義域の元 x について domF(x) : x ∈ dom(F) ↔ ...,  値 F(x) = valF
function flimOp(k, F, c, al, rfF, crL, alR, pnF, seqBody) {
  const sq = X.gen(X.assume(k, 'Seq(a)', (sa, c1) => X.assume(c1, `Conv(a,${c})`, (ha, c2) => X.assume(c2, `all n. (n in Nat -> a[n] in dom(${F}) & a[n] != ${c})`, (hd, c3) =>
    seqBody(c3, sa, ha, hd)))), 'a');
  return use('SeqCritInv', [F, c, al], k, [rfF, crL, alR, pnF, sq]);
}
// compseq(F,a) の値を書き換えて ConvExt
function convByValues(c3, F, sa, hd, rfF, valF, target, other, otherConv, valOther) {
  // valF(n) : c ⊢ F[a[n]] = ... ;  valOther(n): c ⊢ other[n] = ...
  const dom1 = X.gen(X.assume(c3, 'n in Nat', (hn, cn) => X.tc(cn, [X.inst(hd, ['n']), hn], `a[n] in dom(${F})`)), 'n');
  const cs = use('CompSeq', [F, 'a'], c3, [rfF, sa, dom1]);
  const eq = X.gen(X.assume(c3, 'n in Nat', (hn, cn) => {
    const v = X.tc(cn, [X.inst(X.tc(cn, [cs], `all n. (n in Nat -> compseq(${F},a)[n] = ${F}[a[n]])`), ['n']), hn], `compseq(${F},a)[n] = ${F}[a[n]]`);
    return X.sym(X.trans(v, X.trans(valF(cn, hn), X.sym(valOther(cn, hn)), cn), cn));
  }), 'n');
  return use('ConvExt', [other, `compseq(${F},a)`, target], c3, [X.tc(c3, [cs], `Seq(compseq(${F},a))`), eq, otherConv]);
}
const compVal = (cn, f, hn, rf, sa, domf) => { // compseq(f,a)[n] = f[a[n]]
  const cs = use('CompSeq', [f, 'a'], cn, [rf, sa, domf]);
  return X.tc(cn, [X.inst(X.tc(cn, [cs], `all n. (n in Nat -> compseq(${f},a)[n] = ${f}[a[n]])`), ['n']), hn], `compseq(${f},a)[n] = ${f}[a[n]]`);
};
const domOf = (c3, hd, f, F, domIff) => X.gen(X.assume(c3, 'n in Nat', (hn, cn) =>
  X.tc(cn, [X.inst(hd, ['n']), hn, X.inst(domIff, ['a[n]'])], `a[n] in dom(${f})`)), 'n');
const domNe = (c3, hd, f, F, domIff, c) => X.gen(X.assume(c3, 'n in Nat', (hn, cn) =>
  X.tc(cn, [X.inst(hd, ['n']), hn, X.inst(domIff, ['a[n]'])], `a[n] in dom(${f}) & a[n] != ${c}`)), 'n');

function flimBin(name, label, op, opF, limThm, valExpr, seqOp) {
  const F = `${opF}(f,g)`;
  prove(name, `all f. all g. all c. all al. all be. (FLim(f,c,al) -> FLim(g,c,be) -> FLim(${F}, c, ${op}))`, label, () => X.genAll(
    X.assume([], 'FLim(f,c,al)', (hf, k1) => X.assume(k1, 'FLim(g,c,be)', (hg, k) => {
      const rf = use('FLimRFn', ['f', 'c', 'al'], k, [hf]), rg = use('FLimRFn', ['g', 'c', 'be'], k, [hg]);
      const cr = use('FLimCR', ['f', 'c', 'al'], k, [hf]), ar = use('FLimAR', ['f', 'c', 'al'], k, [hf]), br = use('FLimAR', ['g', 'c', 'be'], k, [hg]);
      const FA = use(opF === 'fadd' ? 'FAdd' : 'FMul', ['f', 'g'], k, [rf, rg]);
      const rF = X.tc(k, [FA], `RFn(${F})`);
      const domIff = X.tc(k, [FA], `all x. (x in dom(${F}) <-> x in dom(f) & x in dom(g))`);
      const valF = X.tc(k, [FA], `all x. (x in dom(${F}) -> ${F}[x] = ${valExpr('f[x]', 'g[x]')})`);
      const pn = X.exE(use('PNbhdInter', ['f', 'g', 'c'], k, [use('FLimNb', ['f', 'c', 'al'], k, [hf]), use('FLimNb', ['g', 'c', 'be'], k, [hg])]), 'd', (hd, cd) => {
        const all = X.gen(X.assume(cd, 'x in Real', (hx, c1) => X.assume(c1, '0 < abs(x - c)', (hp, c2) => X.assume(c2, 'abs(x - d) < d'.replace('x - d', 'x - c'), (hl, c3) =>
          X.tc(c3, [X.inst(X.tc(c3, [hd], NB('c', 'd', 'x in dom(f) & x in dom(g)')), ['x']), hx, hp, hl, X.inst(domIff, ['x'])], `x in dom(${F})`)))), 'x');
        return X.tc(cd, [PN(F, 'c'), X.exI(X.tc(cd, [hd, all], `d in Real & 0 < d & ${NB('c', 'd', `x in dom(${F})`)}`), 'r', `r in Real & 0 < r & ${NB('c', 'r', `x in dom(${F})`)}`, 'd')], `PNbhd(${F}, c)`);
      }, k);
      return flimOp(k, F, 'c', op, rF, cr, mem(k, op, [ar, br]), pn, (c3, sa, ha, hd) => {
        const df = domNe(c3, hd, 'f', F, domIff, 'c'), dg = domNe(c3, hd, 'g', F, domIff, 'c');
        const cf = use('SeqCrit', ['f', 'c', 'al', 'a'], c3, [hf, ha, df]), cg = use('SeqCrit', ['g', 'c', 'be', 'a'], c3, [hg, ha, dg]);
        const sf = use('ConvSeq', ['compseq(f,a)', 'al'], c3, [cf]), sg = use('ConvSeq', ['compseq(g,a)', 'be'], c3, [cg]);
        const other = `${seqOp}(compseq(f,a), compseq(g,a))`;
        const lim = use(limThm, ['compseq(f,a)', 'al', 'compseq(g,a)', 'be'], c3, [cf, cg]);
        const ops = use(seqOp === 'oplus' ? 'Oplus' : 'Otimes', ['compseq(f,a)', 'compseq(g,a)'], c3, [sf, sg]);
        const df1 = domOf(c3, hd, 'f', F, domIff), dg1 = domOf(c3, hd, 'g', F, domIff);
        return convByValues(c3, F, sa, hd, rF,
          (cn, hn) => X.tc(cn, [X.inst(valF, ['a[n]']), X.inst(hd, ['n']), hn], `${F}[a[n]] = ${valExpr('f[a[n]]', 'g[a[n]]')}`),
          op, other, lim,
          (cn, hn) => {
            const v = X.tc(cn, [X.inst(X.tc(cn, [ops], `all n. (n in Nat -> ${other}[n] = ${valExpr('compseq(f,a)[n]', 'compseq(g,a)[n]')})`), ['n']), hn], `${other}[n] = ${valExpr('compseq(f,a)[n]', 'compseq(g,a)[n]')}`);
            return X.trans(X.trans(v, K.cong(compVal(cn, 'f', hn, rf, sa, df1), valExpr('compseq(f,a)[n]', 'compseq(g,a)[n]'), cn), cn),
              K.cong(compVal(cn, 'g', hn, rg, sa, dg1), valExpr('f[a[n]]', 'compseq(g,a)[n]'), cn), cn);
          });
      });
    })), ['f', 'g', 'c', 'al', 'be']));
}
flimBin('FLimAdd', '定理1.8(1)', 'al + be', 'fadd', 'LimSum', (x, y) => `${x} + ${y}`, 'oplus');
flimBin('FLimMul', '定理1.8(2)', 'al * be', 'fmul', 'LimProd', (x, y) => `${x} * ${y}`, 'otimes');

prove('FLimScal', 'all l. all f. all c. all al. (l in Real -> FLim(f,c,al) -> FLim(fscal(l,f), c, l * al))', '定理1.8(1\')', () => X.genAll(
  X.assume([], 'l in Real', (hl0, k1) => X.assume(k1, 'FLim(f,c,al)', (hf, k) => {
    const F = 'fscal(l,f)';
    const rf = use('FLimRFn', ['f', 'c', 'al'], k, [hf]), cr = use('FLimCR', ['f', 'c', 'al'], k, [hf]), ar = use('FLimAR', ['f', 'c', 'al'], k, [hf]);
    const FS = use('FScal', ['l', 'f'], k, [hl0, rf]);
    const rF = X.tc(k, [FS], `RFn(${F})`);
    const domIff = X.tc(k, [FS], `all x. (x in dom(${F}) <-> x in dom(f))`);
    const valF = X.tc(k, [FS], `all x. (x in dom(${F}) -> ${F}[x] = l * f[x])`);
    const pnf = X.tc(k, [use('FLimNb', ['f', 'c', 'al'], k, [hf]), PN('f', 'c')], `ex r. (r in Real & 0 < r & ${NB('c', 'r', 'x in dom(f)')})`);
    const pn = X.exE(pnf, 'r', (hr, cr2) => {
      const all = X.gen(X.assume(cr2, 'x in Real', (hx, c1) => X.assume(c1, '0 < abs(x - c)', (hp, c2) => X.assume(c2, 'abs(x - c) < r', (hl, c3) =>
        X.tc(c3, [X.inst(X.tc(c3, [hr], NB('c', 'r', 'x in dom(f)')), ['x']), hx, hp, hl, X.inst(domIff, ['x'])], `x in dom(${F})`)))), 'x');
      return X.tc(cr2, [PN(F, 'c'), X.exI(X.tc(cr2, [hr, all], `r in Real & 0 < r & ${NB('c', 'r', `x in dom(${F})`)}`), 'r', `r in Real & 0 < r & ${NB('c', 'r', `x in dom(${F})`)}`, 'r')], `PNbhd(${F}, c)`);
    }, k);
    return flimOp(k, F, 'c', 'l * al', rF, cr, mem(k, 'l * al', [hl0, ar]), pn, (c3, sa, ha, hd) => {
      const df = domNe(c3, hd, 'f', F, domIff, 'c');
      const cf = use('SeqCrit', ['f', 'c', 'al', 'a'], c3, [hf, ha, df]);
      const sf = use('ConvSeq', ['compseq(f,a)', 'al'], c3, [cf]);
      const other = 'odot(l, compseq(f,a))';
      const lim = use('LimScalar', ['l', 'compseq(f,a)', 'al'], c3, [hl0, cf]);
      const ops = use('Odot', ['l', 'compseq(f,a)'], c3, [hl0, sf]);
      const df1 = domOf(c3, hd, 'f', F, domIff);
      return convByValues(c3, F, sa, hd, rF,
        (cn, hn) => X.tc(cn, [X.inst(valF, ['a[n]']), X.inst(hd, ['n']), hn], `${F}[a[n]] = l * f[a[n]]`),
        'l * al', other, lim,
        (cn, hn) => {
          const v = X.tc(cn, [X.inst(X.tc(cn, [ops], `all n. (n in Nat -> ${other}[n] = l * compseq(f,a)[n])`), ['n']), hn], `${other}[n] = l * compseq(f,a)[n]`);
          return X.trans(v, K.cong(compVal(cn, 'f', hn, rf, sa, df1), 'l * compseq(f,a)[n]', cn), cn);
        });
    });
  })), ['l', 'f', 'c', 'al']));

prove('FLimDiv', 'all f. all g. all c. all al. all be. (FLim(f,c,al) -> FLim(g,c,be) -> be != 0 -> FLim(fdiv(f,g), c, al * be^-1))', '定理1.8(3)', () => X.genAll(
  X.assume([], 'FLim(f,c,al)', (hf, k1) => X.assume(k1, 'FLim(g,c,be)', (hg, k2) => X.assume(k2, 'be != 0', (hz, k) => {
    const F = 'fdiv(f,g)';
    const rf = use('FLimRFn', ['f', 'c', 'al'], k, [hf]), rg = use('FLimRFn', ['g', 'c', 'be'], k, [hg]);
    const cr = use('FLimCR', ['f', 'c', 'al'], k, [hf]), ar = use('FLimAR', ['f', 'c', 'al'], k, [hf]), br = use('FLimAR', ['g', 'c', 'be'], k, [hg]);
    const FD = use('FDiv', ['f', 'g'], k, [rf, rg]);
    const rF = X.tc(k, [FD], `RFn(${F})`);
    const domIff = X.tc(k, [FD], `all x. (x in dom(${F}) <-> x in dom(f) & x in dom(g) & g[x] != 0)`);
    const valF = X.tc(k, [FD], `all x. (x in dom(${F}) -> ${F}[x] = f[x] * g[x]^-1)`);
    const bp = use('AbsPos', ['be'], k, [br, hz]);
    const h2 = 'abs(be) * 2^-1';
    const hp2 = use('HalfPos', ['abs(be)'], k, [br, bp]);
    // g の値が 0 にならない近傍
    const gne = X.exE(use('FLimE', ['g', 'c', 'be', h2], k, [hg, mem(k, h2, [br]), hp2]), 'de', (hde, cde) => {
      const der = X.tc(cde, [hde], 'de in Real'), dep = X.tc(cde, [hde], '0 < de');
      const gall = X.tc(cde, [hde], `all x. (x in dom(g) -> 0 < abs(x - c) -> abs(x - c) < de -> abs(g[x] - be) < ${h2})`);
      return X.exE(use('PNbhdInter', ['f', 'g', 'c'], cde, [use('FLimNb', ['f', 'c', 'al'], cde, [hf]), use('FLimNb', ['g', 'c', 'be'], cde, [hg])]), 'd', (hd, cd) => {
        const dr = X.tc(cd, [hd], 'd in Real');
        return X.exE(use('MinPos', ['d', 'de'], cd, [dr, der, X.tc(cd, [hd], '0 < d'), dep]), 'r', (hr, cr3) => {
          const all = X.gen(X.assume(cr3, 'x in Real', (hx, c1) => X.assume(c1, '0 < abs(x - c)', (hp, c2) => X.assume(c2, 'abs(x - c) < r', (hl, c3) => {
            const fg = X.tc(c3, [X.inst(X.tc(c3, [hd], NB('c', 'd', 'x in dom(f) & x in dom(g)')), ['x']), hx, hp, use('LtLeTrans', ['abs(x - c)', 'r', 'd'], c3, [hl, X.tc(c3, [hr], 'r <= d')])], 'x in dom(f) & x in dom(g)');
            const gx = X.tc(c3, [X.inst(gall, ['x']), fg, hp, use('LtLeTrans', ['abs(x - c)', 'r', 'de'], c3, [hl, X.tc(c3, [hr], 'r <= de')])], `abs(g[x] - be) < ${h2}`);
            const xd = X.tc(c3, [fg], 'x in dom(g)');
            const low = use('AbsLowerHalf', ['g[x]', 'be'], c3, [mem(c3, 'g[x]', [rg, xd]), br, gx]);
            const nz = X.raa(c3, 'g[x] != 0', (hn, c4) => {
              const e = X.tc(c4, [hn], 'g[x] = 0');
              const z = calc(c4, 'abs(g[x])', [['abs(0)', e], ['0', use('AbsOfNonneg', ['0'], c4, [X.tc(c4, [X.refl('0')], '0 <= 0')])]]);
              return [use('LtTrans', ['0', h2, 'abs(g[x])'], c4, [hp2, low]), X.rw(X.sym(z), X.inst(X.thm('LtIrrefl'), ['0']), '~ 0 < abs(g[x])', c4)];
            });
            return X.tc(c3, [fg, nz, X.inst(domIff, ['x'])], `x in dom(${F})`);
          }))), 'x');
          return X.tc(cr3, [PN(F, 'c'), X.exI(X.tc(cr3, [hr, all], `r in Real & 0 < r & ${NB('c', 'r', `x in dom(${F})`)}`), 'r', `r in Real & 0 < r & ${NB('c', 'r', `x in dom(${F})`)}`, 'r')], `PNbhd(${F}, c)`);
        }, cd);
      }, cde);
    }, k);
    const op = 'al * be^-1';
    return flimOp(k, F, 'c', op, rF, cr, mem(k, op, [ar, br, hz]), gne, (c3, sa, ha, hd) => {
      const domF = X.gen(X.assume(c3, 'n in Nat', (hn, cn) => X.tc(cn, [X.inst(hd, ['n']), hn, X.inst(domIff, ['a[n]'])], 'a[n] in dom(f) & a[n] in dom(g) & g[a[n]] != 0 & a[n] != c')), 'n');
      const df = X.gen(X.assume(c3, 'n in Nat', (hn, cn) => X.tc(cn, [X.inst(domF, ['n']), hn], 'a[n] in dom(f) & a[n] != c')), 'n');
      const dg = X.gen(X.assume(c3, 'n in Nat', (hn, cn) => X.tc(cn, [X.inst(domF, ['n']), hn], 'a[n] in dom(g) & a[n] != c')), 'n');
      const df1 = domOf(c3, hd, 'f', F, domIff), dg1 = X.gen(X.assume(c3, 'n in Nat', (hn, cn) => X.tc(cn, [X.inst(domF, ['n']), hn], 'a[n] in dom(g)')), 'n');
      const cf = use('SeqCrit', ['f', 'c', 'al', 'a'], c3, [hf, ha, df]), cg = use('SeqCrit', ['g', 'c', 'be', 'a'], c3, [hg, ha, dg]);
      const sf = use('ConvSeq', ['compseq(f,a)', 'al'], c3, [cf]), sg = use('ConvSeq', ['compseq(g,a)', 'be'], c3, [cg]);
      const gnz = X.gen(X.assume(c3, 'n in Nat', (hn, cn) => X.rw(X.sym(compVal(cn, 'g', hn, rg, sa, dg1)), X.tc(cn, [X.inst(domF, ['n']), hn], 'g[a[n]] != 0'), 'compseq(g,a)[n] != 0', cn)), 'n');
      const lim = use('LimQuot', ['compseq(f,a)', 'al', 'compseq(g,a)', 'be'], c3, [cf, cg, hz, gnz]);
      const rc = use('Recip', ['compseq(g,a)'], c3, [sg, gnz]);
      const src = X.tc(c3, [rc], 'Seq(recip(compseq(g,a)))');
      const other = 'otimes(compseq(f,a), recip(compseq(g,a)))';
      const ops = use('Otimes', ['compseq(f,a)', 'recip(compseq(g,a))'], c3, [sf, src]);
      return convByValues(c3, F, sa, hd, rF,
        (cn, hn) => X.tc(cn, [X.inst(valF, ['a[n]']), X.inst(hd, ['n']), hn], `${F}[a[n]] = f[a[n]] * g[a[n]]^-1`),
        op, other, lim,
        (cn, hn) => {
          const v = X.tc(cn, [X.inst(X.tc(cn, [ops], `all n. (n in Nat -> ${other}[n] = compseq(f,a)[n] * recip(compseq(g,a))[n])`), ['n']), hn], `${other}[n] = compseq(f,a)[n] * recip(compseq(g,a))[n]`);
          const r = X.tc(cn, [X.inst(X.tc(cn, [rc], 'all n. (n in Nat -> recip(compseq(g,a))[n] = compseq(g,a)[n]^-1)'), ['n']), hn], 'recip(compseq(g,a))[n] = compseq(g,a)[n]^-1');
          return calc(cn, `${other}[n]`, [['compseq(f,a)[n] * recip(compseq(g,a))[n]', v], ['compseq(f,a)[n] * compseq(g,a)[n]^-1', r],
            ['f[a[n]] * compseq(g,a)[n]^-1', compVal(cn, 'f', hn, rf, sa, df1)], ['f[a[n]] * g[a[n]]^-1', compVal(cn, 'g', hn, rg, sa, dg1)]]);
        });
    });
  }))), ['f', 'g', 'c', 'al', 'be']));

// ---------------- 定理 1.9 ----------------
prove('FLimLe', 'all f. all g. all c. all al. all be. all r. (FLim(f,c,al) -> FLim(g,c,be) -> r in Real -> 0 < r -> (all x. (x in dom(f) -> x in dom(g) -> 0 < abs(x - c) -> abs(x - c) < r -> f[x] <= g[x])) -> al <= be)', '定理1.9', () => X.genAll(
  X.assume([], 'FLim(f,c,al)', (hf, k1) => X.assume(k1, 'FLim(g,c,be)', (hg, k2) => X.assume(k2, 'r in Real', (hr, k3) => X.assume(k3, '0 < r', (hrp, k4) => X.assume(k4, 'all x. (x in dom(f) -> x in dom(g) -> 0 < abs(x - c) -> abs(x - c) < r -> f[x] <= g[x])', (hle, k) => {
    const rf = use('FLimRFn', ['f', 'c', 'al'], k, [hf]), rg = use('FLimRFn', ['g', 'c', 'be'], k, [hg]);
    const cr = use('FLimCR', ['f', 'c', 'al'], k, [hf]);
    return X.exE(use('PNbhdInter', ['f', 'g', 'c'], k, [use('FLimNb', ['f', 'c', 'al'], k, [hf]), use('FLimNb', ['g', 'c', 'be'], k, [hg])]), 'd', (hd, cd) => {
      const dr = X.tc(cd, [hd], 'd in Real');
      return X.exE(use('MinPos', ['d', 'r'], cd, [dr, hr, X.tc(cd, [hd], '0 < d'), hrp]), 'rho', (hq, cq) => {
        const qr = X.tc(cq, [hq], 'rho in Real');
        return X.exE(use('ApproxSeq', ['c', 'rho'], cq, [cr, qr, X.tc(cq, [hq], '0 < rho')]), 'a', (ha, ca) => {
          const sa = X.tc(ca, [ha], 'Seq(a)'), conv = X.tc(ca, [ha], 'Conv(a,c)');
          const near = X.tc(ca, [ha], 'all n. (n in Nat -> 0 < abs(a[n] - c) & abs(a[n] - c) < rho)');
          const info = (cn, hn) => {
            const p = X.tc(cn, [X.inst(near, ['n']), hn], '0 < abs(a[n] - c) & abs(a[n] - c) < rho');
            const lt = X.tc(cn, [p], 'abs(a[n] - c) < rho');
            const xr = mem(cn, 'a[n]', [sa, hn]);
            const fg = X.tc(cn, [X.inst(X.tc(cn, [hd], NB('c', 'd', 'x in dom(f) & x in dom(g)')), ['a[n]']), xr, p, use('LtLeTrans', ['abs(a[n] - c)', 'rho', 'd'], cn, [lt, X.tc(cn, [hq], 'rho <= d')])], 'a[n] in dom(f) & a[n] in dom(g)');
            const ne = use('PosAbsNe', ['a[n]', 'c'], cn, [xr, cr, X.tc(cn, [p], '0 < abs(a[n] - c)')]);
            return { p, lt, fg, ne };
          };
          const df = X.gen(X.assume(ca, 'n in Nat', (hn, cn) => { const { fg, ne } = info(cn, hn); return X.tc(cn, [fg, ne], 'a[n] in dom(f) & a[n] != c'); }), 'n');
          const dg = X.gen(X.assume(ca, 'n in Nat', (hn, cn) => { const { fg, ne } = info(cn, hn); return X.tc(cn, [fg, ne], 'a[n] in dom(g) & a[n] != c'); }), 'n');
          const df1 = X.gen(X.assume(ca, 'n in Nat', (hn, cn) => X.tc(cn, [X.inst(df, ['n']), hn], 'a[n] in dom(f)')), 'n');
          const dg1 = X.gen(X.assume(ca, 'n in Nat', (hn, cn) => X.tc(cn, [X.inst(dg, ['n']), hn], 'a[n] in dom(g)')), 'n');
          const cf = use('SeqCrit', ['f', 'c', 'al', 'a'], ca, [hf, conv, df]), cg = use('SeqCrit', ['g', 'c', 'be', 'a'], ca, [hg, conv, dg]);
          const les = X.gen(X.assume(ca, 'n in Nat', (hn, cn) => {
            const { p, lt, fg } = info(cn, hn);
            const l = X.tc(cn, [X.inst(hle, ['a[n]']), fg, p, use('LtLeTrans', ['abs(a[n] - c)', 'rho', 'r'], cn, [lt, X.tc(cn, [hq], 'rho <= r')])], 'f[a[n]] <= g[a[n]]');
            return X.rw(X.sym(compVal(cn, 'g', hn, rg, sa, dg1)), X.rw(X.sym(compVal(cn, 'f', hn, rf, sa, df1)), l, 'compseq(f,a)[n] <= g[a[n]]', cn), 'compseq(f,a)[n] <= compseq(g,a)[n]', cn);
          }), 'n');
          return use('LimLe', ['compseq(f,a)', 'compseq(g,a)', 'al', 'be'], ca, [cf, cg, les]);
        }, cq);
      }, cd);
    }, k);
  }))))), ['f', 'g', 'c', 'al', 'be', 'r']));

// ---------------- 定理 1.13: Cauchy の収束判定法 ----------------
const CCRIT = 'all eps. (eps in Real -> 0 < eps -> ex de. (de in Real & 0 < de & all x. all y. (x in dom(f) -> y in dom(f) -> 0 < abs(x - c) -> abs(x - c) < de -> 0 < abs(y - c) -> abs(y - c) < de -> abs(f[x] - f[y]) < eps)))';
const CQf = 'all x. all y. (x in dom(f) -> y in dom(f) -> 0 < abs(x - c) -> abs(x - c) < de -> 0 < abs(y - c) -> abs(y - c) < de -> abs(f[x] - f[y]) < eps)';
prove('FCauchy', `all f. all c. (RFn(f) -> c in Real -> PNbhd(f,c) -> ((ex al. FLim(f,c,al)) <-> ${CCRIT}))`, '定理1.13', () => X.genAll(
  X.assume([], 'RFn(f)', (rf, k1) => X.assume(k1, 'c in Real', (cr, k2) => X.assume(k2, 'PNbhd(f,c)', (pn, k) => {
    const fw = X.assume(k, 'ex al. FLim(f,c,al)', (hx, c0) => X.exE(hx, 'al', (hf, ck) => {
      const ar = use('FLimAR', ['f', 'c', 'al'], ck, [hf]);
      return X.gen(X.assume(ck, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => {
        const e = 'eps * 2^-1';
        return X.exE(use('FLimE', ['f', 'c', 'al', e], c2, [hf, mem(c2, e, [he]), use('HalfPos', ['eps'], c2, [he, hp])]), 'de', (hd, cd) => {
          const fa = X.tc(cd, [hd], `all x. (x in dom(f) -> 0 < abs(x - c) -> abs(x - c) < de -> abs(f[x] - al) < ${e})`);
          const body = X.gen(X.gen(X.assume(cd, 'x in dom(f)', (h1, d1) => X.assume(d1, 'y in dom(f)', (h2, d2) => X.assume(d2, '0 < abs(x - c)', (h3, d3) => X.assume(d3, 'abs(x - c) < de', (h4, d4) =>
            X.assume(d4, '0 < abs(y - c)', (h5, d5) => X.assume(d5, 'abs(y - c) < de', (h6, d6) => {
              const g = [ar, he, mem(d6, 'f[x]', [rf, h1]), mem(d6, 'f[y]', [rf, h2])];
              const a1 = X.rw(use('AbsSubComm', ['f[x]', 'al'], d6, g), X.tc(d6, [X.inst(fa, ['x']), h1, h3, h4], `abs(f[x] - al) < ${e}`), `abs(al - f[x]) < ${e}`, d6);
              const a2 = X.rw(use('AbsSubComm', ['f[y]', 'al'], d6, g), X.tc(d6, [X.inst(fa, ['y']), h2, h5, h6], `abs(f[y] - al) < ${e}`), `abs(al - f[y]) < ${e}`, d6);
              return X.rw(use('HalfSum', ['eps'], d6, g), use('ErrTwo', ['al', 'f[x]', 'f[y]', e], d6, [...g, mem(d6, e, g), a1, a2]), 'abs(f[x] - f[y]) < eps', d6);
            })))))), 'y'), 'x');
          return X.exI(X.tc(cd, [hd, body], `de in Real & 0 < de & ${CQf}`), 'de', `de in Real & 0 < de & ${CQf}`, 'de');
        });
      })), 'eps');
    }, c0));
    const bw = X.assume(k, CCRIT, (hc, c0) => {
      const cq = (cc, e, he, hp) => X.tc(cc, [X.inst(hc, [e]), he, hp], `ex de. (de in Real & 0 < de & ${CQf.replace(/eps/g, e)})`);
      const pr = X.tc(c0, [pn, PN('f', 'c')], `ex r. (r in Real & 0 < r & ${NB('c', 'r', 'x in dom(f)')})`);
      return X.exE(pr, 'r', (hr, cr0) => X.exE(use('ApproxSeq', ['c', 'r'], cr0, [cr, X.tc(cr0, [hr], 'r in Real'), X.tc(cr0, [hr], '0 < r')]), 'p', (hpq, cp) => {
        const sp = X.tc(cp, [hpq], 'Seq(p)'), convp = X.tc(cp, [hpq], 'Conv(p,c)');
        const near = X.tc(cp, [hpq], 'all n. (n in Nat -> 0 < abs(p[n] - c) & abs(p[n] - c) < r)');
        const pinfo = (cn, n, hn) => {
          const q = X.tc(cn, [X.inst(near, [n]), hn], `0 < abs(p[${n}] - c) & abs(p[${n}] - c) < r`);
          const xr = mem(cn, `p[${n}]`, [sp, hn]);
          const d = X.tc(cn, [X.inst(X.tc(cn, [hr], NB('c', 'r', 'x in dom(f)')), [`p[${n}]`]), xr, q], `p[${n}] in dom(f)`);
          return { q, d };
        };
        const dp1 = X.gen(X.assume(cp, 'n in Nat', (hn, cn) => pinfo(cn, 'n', hn).d), 'n');
        const csq = use('CompSeq', ['f', 'p'], cp, [rf, sp, dp1]);
        const fpv = (cn, n, hn) => X.tc(cn, [X.inst(X.tc(cn, [csq], 'all n. (n in Nat -> compseq(f,p)[n] = f[p[n]])'), [n]), hn], `compseq(f,p)[${n}] = f[p[${n}]]`);
        // f∘p は Cauchy 列
        const cau = X.tc(cp, [X.inst(X.defAx('Cauchy'), ['compseq(f,p)']), X.tc(cp, [csq], 'Seq(compseq(f,p))'), X.gen(X.assume(cp, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) =>
          X.exE(cq(c2, 'eps', he, hp), 'de', (hd, cd) => X.exE(use('ConvE', ['p', 'c', 'de'], cd, [convp, X.tc(cd, [hd], 'de in Real'), X.tc(cd, [hd], '0 < de')]), 'N', (hN, cN) => {
            const body = X.gen(X.gen(X.assume(cN, 'm in Nat', (hm, d1) => X.assume(d1, 'n in Nat', (hn, d2) => X.assume(d2, 'N <= m', (l1, d3) => X.assume(d3, 'N <= n', (l2, d4) => {
              const pm = pinfo(d4, 'm', hm), pnn = pinfo(d4, 'n', hn);
              const am = tailAt(d4, hN, 'N', n => `abs(p[${n}] - c) < de`, 'm', hm, l1), an = tailAt(d4, hN, 'N', n => `abs(p[${n}] - c) < de`, 'n', hn, l2);
              const l = X.tc(d4, [X.inst(X.tc(d4, [hd], CQf), ['p[m]', 'p[n]']), pm.d, pnn.d, pm.q, am, pnn.q, an], 'abs(f[p[m]] - f[p[n]]) < eps');
              return X.rw(X.sym(fpv(d4, 'n', hn)), X.rw(X.sym(fpv(d4, 'm', hm)), l, 'abs(compseq(f,p)[m] - f[p[n]]) < eps', d4), 'abs(compseq(f,p)[m] - compseq(f,p)[n]) < eps', d4);
            })))), 'n'), 'm');
            const G = 'N in Nat & all m. all n. (m in Nat -> n in Nat -> N <= m -> N <= n -> abs(compseq(f,p)[m] - compseq(f,p)[n]) < eps)';
            return X.exI(X.tc(cN, [X.tc(cN, [hN], 'N in Nat'), body], G), 'N', G, 'N');
          }, cd)))), 'eps')], 'Cauchy(compseq(f,p))');
        const cg = X.tc(cp, [use('CauchyComplete', ['compseq(f,p)'], cp), cau, X.inst(X.defAx('Cgt'), ['compseq(f,p)'])], 'ex al. Conv(compseq(f,p), al)');
        return X.exE(cg, 'al', (ha, ca) => {
          const ar = use('ConvR', ['compseq(f,p)', 'al'], ca, [ha]);
          const eps = X.gen(X.assume(ca, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => {
            const e = 'eps * 2^-1';
            const er = mem(c2, e, [he]), ep = use('HalfPos', ['eps'], c2, [he, hp]);
            return X.exE(cq(c2, e, er, ep), 'de', (hd, cd) => {
              const der = X.tc(cd, [hd], 'de in Real'), dep = X.tc(cd, [hd], '0 < de');
              return X.exE(use('Tail', ['p', 'c', 'compseq(f,p)', 'al', 'de'], cd, [convp, ha, der, dep]), 'N0', (h0, c0b) => {
                // ε/2 に対する N1 も必要なので, ConvE をもう一度
                return X.exE(use('ConvE', ['compseq(f,p)', 'al', e], c0b, [ha, er, ep]), 'N1', (h1, c1b) => {
                  const n0 = X.tc(c1b, [h0], 'N0 in Nat'), n1 = X.tc(c1b, [h1], 'N1 in Nat');
                  const M = 'cup(N0, N1)';
                  const mn = use('NatCup', ['N0', 'N1'], c1b, [n0, n1]);
                  const t0 = tailAt(c1b, h0, 'N0', n => `abs(p[${n}] - c) < de & abs(compseq(f,p)[${n}] - al) < de`, M, mn, X.inst(X.thm('LeCupL'), ['N0', 'N1']));
                  const t1 = tailAt(c1b, h1, 'N1', n => `abs(compseq(f,p)[${n}] - al) < ${e}`, M, mn, X.inst(X.thm('LeCupR'), ['N0', 'N1']));
                  const pm = pinfo(c1b, M, mn);
                  const t1b = X.rw(fpv(c1b, M, mn), t1, `abs(f[p[${M}]] - al) < ${e}`, c1b);
                  const all = X.gen(X.assume(c1b, 'x in dom(f)', (hx, d1) => X.assume(d1, '0 < abs(x - c)', (hp1, d2) => X.assume(d2, 'abs(x - c) < de', (hl, d3) => {
                    const g = [ar, he, mem(d3, 'f[x]', [rf, hx]), mem(d3, `f[p[${M}]]`, [rf, pm.d]), er];
                    const l = X.tc(d3, [X.inst(X.tc(d3, [hd], CQf.replace(/eps/g, e)), ['x', `p[${M}]`]), hx, pm.d, hp1, hl, pm.q, X.tc(d3, [t0], `abs(p[${M}] - c) < de`)], `abs(f[x] - f[p[${M}]]) < ${e}`);
                    return X.rw(use('HalfSum', ['eps'], d3, g), use('ErrChain', ['f[x]', `f[p[${M}]]`, 'al', e], d3, [...g, l, t1b]), 'abs(f[x] - al) < eps', d3);
                  }))), 'x');
                  return X.exI(X.tc(c1b, [hd, all], `de in Real & 0 < de & all x. (x in dom(f) -> 0 < abs(x - c) -> abs(x - c) < de -> abs(f[x] - al) < eps)`), 'de',
                    'de in Real & 0 < de & all x. (x in dom(f) -> 0 < abs(x - c) -> abs(x - c) < de -> abs(f[x] - al) < eps)', 'de');
                }, c0b);
              }, cd);
            }, c2);
          })), 'eps');
          const fl = X.tc(ca, [X.inst(X.defAx('FLim'), ['f', 'c', 'al']), rf, cr, ar, pn, eps], 'FLim(f,c,al)');
          return X.exI(fl, 'al', 'FLim(f,c,al)', 'al');
        }, cp);
      }, cr0), c0);
    });
    return X.tc(k, [fw, bw], `(ex al. FLim(f,c,al)) <-> ${CCRIT}`);
  }))), ['f', 'c']));

// ---------------- 片側極限 (定義 1.15, 1.16, 定理 1.19) ----------------
def('RNbhd', 'all f. all c. (RNbhd(f,c) <-> ex r. (r in Real & 0 < r & all x. (x in Real -> c < x -> x < c + r -> x in dom(f))))', 'DefRNbhd');
def('LNbhd', 'all f. all c. (LNbhd(f,c) <-> ex r. (r in Real & 0 < r & all x. (x in Real -> c - r < x -> x < c -> x in dom(f))))', 'DefLNbhd');
def('FLimR', 'all f. all c. all al. (FLimR(f,c,al) <-> RFn(f) & c in Real & al in Real & RNbhd(f,c) & all eps. (eps in Real -> 0 < eps -> ex de. (de in Real & 0 < de & all x. (x in dom(f) -> c < x -> x < c + de -> abs(f[x] - al) < eps))))', 'DefFLimR');
def('FLimL', 'all f. all c. all al. (FLimL(f,c,al) <-> RFn(f) & c in Real & al in Real & LNbhd(f,c) & all eps. (eps in Real -> 0 < eps -> ex de. (de in Real & 0 < de & all x. (x in dom(f) -> c - de < x -> x < c -> abs(f[x] - al) < eps))))', 'DefFLimL');
def('FLimInf', 'all f. all al. (FLimInf(f,al) <-> RFn(f) & al in Real & (ex r. (r in Real & all x. (x in Real -> r < x -> x in dom(f)))) & all eps. (eps in Real -> 0 < eps -> ex L. (L in Real & all x. (x in dom(f) -> L < x -> abs(f[x] - al) < eps))))', 'DefFLimInf');

// c < x < c + d ⇔ 0 < |x - c| < d かつ c < x
prove('RightAbs', 'all x. all c. all d. (x in Real -> c in Real -> d in Real -> c < x -> x < c + d -> 0 < abs(x - c) & abs(x - c) < d)', '[H3]', () => intro(['x', 'c', 'd'], ['c < x', 'x < c + d'], (k, [h1, h2]) => {
  const p = use('SubPos', ['c', 'x'], k, [h1]);
  const ab = use('AbsOfNonneg', ['x - c'], k, [X.tc(k, [p], '0 <= x - c')]);
  const l = use('LtAddSwap', ['c', 'd', 'x'], k, [h2]);
  return X.tc(k, [X.rw(X.sym(ab), p, '0 < abs(x - c)', k), X.rw(X.sym(ab), l, 'abs(x - c) < d', k)], '0 < abs(x - c) & abs(x - c) < d');
}));
prove('LtAddSwap2', 'all c. all d. all x. (c in Real -> d in Real -> x in Real -> c < d + x -> c - d < x)', '[H4]', () => intro(['c', 'd', 'x'], ['c < d + x'], (k, [h]) => {
  const l = use('R14', ['c', 'd + x', '-d'], k, [h]);
  const e = calc(k, '(d + x) + -d', [['(x + d) + -d', use('R3', ['d', 'x'], k)], ['x + (d + -d)', use('R2', ['x', 'd', '-d'], k)], ['x + 0', use('R5', ['d'], k)], ['x', use('R4', ['x'], k)]]);
  return X.rw(X.sym(X.inst(X.defAx('minus'), ['c', 'd'])), X.rw(e, l, 'c + -d < x', k), 'c - d < x', k);
}));
prove('LeftAbs', 'all x. all c. all d. (x in Real -> c in Real -> d in Real -> c - d < x -> x < c -> 0 < abs(x - c) & abs(x - c) < d)', '[H5]', () => intro(['x', 'c', 'd'], ['c - d < x', 'x < c'], (k, [h1, h2]) => {
  const p = use('SubPos', ['x', 'c'], k, [h2]);                  // 0 < c - x
  const ab = X.trans(use('AbsSubComm', ['x', 'c'], k), use('AbsOfNonneg', ['c - x'], k, [X.tc(k, [p], '0 <= c - x')]), k);   // |x - c| = c - x
  const l1 = use('SubLtSwap', ['c', 'd', 'x'], k, [h1]);        // -d < x - c
  const l2 = X.rw(use('SubNeg', ['c', 'x'], k), X.rw(use('NegNeg', ['d'], k), use('NegLt', ['-d', 'x - c'], k, [l1]), '-(x - c) < d', k), 'c - x < d', k);
  return X.tc(k, [X.rw(X.sym(ab), p, '0 < abs(x - c)', k), X.rw(X.sym(ab), l2, 'abs(x - c) < d', k)], '0 < abs(x - c) & abs(x - c) < d');
}));
prove('NeSides', 'all x. all c. (x in Real -> c in Real -> 0 < abs(x - c) -> x < c | c < x)', '[H6]', () => intro(['x', 'c'], ['0 < abs(x - c)'], (k, [h]) =>
  X.tc(k, [use('R13', ['x', 'c'], k), use('PosAbsNe', ['x', 'c'], k, [h])], 'x < c | c < x')));
prove('SideR', 'all x. all c. all d. (x in Real -> c in Real -> d in Real -> c < x -> abs(x - c) < d -> x < c + d)', '[H7]', () => intro(['x', 'c', 'd'], ['c < x', 'abs(x - c) < d'], (k, [h1, h2]) => {
  const ab = use('AbsOfNonneg', ['x - c'], k, [X.tc(k, [use('SubPos', ['c', 'x'], k, [h1])], '0 <= x - c')]);
  const l = use('LtSubAdd', ['x', 'c', 'd'], k, [X.rw(ab, h2, 'x - c < d', k)]);
  return X.rw(use('R3', ['d', 'c'], k), l, 'x < c + d', k);
}));
prove('SideL', 'all x. all c. all d. (x in Real -> c in Real -> d in Real -> x < c -> abs(x - c) < d -> c - d < x)', '[H8]', () => intro(['x', 'c', 'd'], ['x < c', 'abs(x - c) < d'], (k, [h1, h2]) => {
  const ab = X.trans(use('AbsSubComm', ['x', 'c'], k), use('AbsOfNonneg', ['c - x'], k, [X.tc(k, [use('SubPos', ['x', 'c'], k, [h1])], '0 <= c - x')]), k);
  const l = use('LtSubAdd', ['c', 'x', 'd'], k, [X.rw(ab, h2, 'c - x < d', k)]);   // c < d + x
  return use('LtAddSwap2', ['c', 'd', 'x'], k, [l]);
}));

const RN = 'all x. (x in Real -> c < x -> x < c + r -> x in dom(f))', LN = 'all x. (x in Real -> c - r < x -> x < c -> x in dom(f))';
const RE = e => `ex de. (de in Real & 0 < de & all x. (x in dom(f) -> c < x -> x < c + de -> abs(f[x] - al) < ${e}))`;
const LE = e => `ex de. (de in Real & 0 < de & all x. (x in dom(f) -> c - de < x -> x < c -> abs(f[x] - al) < ${e}))`;
prove('FLimLR', 'all f. all c. all al. (FLim(f,c,al) <-> FLimR(f,c,al) & FLimL(f,c,al))', '定理1.19', () => X.genAll((() => {
  const dR = X.inst(X.defAx('FLimR'), ['f', 'c', 'al']), dL = X.inst(X.defAx('FLimL'), ['f', 'c', 'al']);
  const fw = X.assume([], 'FLim(f,c,al)', (hf, k) => {
    const rf = use('FLimRFn', ['f', 'c', 'al'], k, [hf]), cr = use('FLimCR', ['f', 'c', 'al'], k, [hf]), ar = use('FLimAR', ['f', 'c', 'al'], k, [hf]);
    const pr = X.tc(k, [use('FLimNb', ['f', 'c', 'al'], k, [hf]), PN('f', 'c')], `ex r. (r in Real & 0 < r & ${NB('c', 'r', 'x in dom(f)')})`);
    const side = (which) => X.exE(pr, 'r', (hr, c1) => {
      const rr = X.tc(c1, [hr], 'r in Real');
      const all = X.gen(X.assume(c1, 'x in Real', (hx, c2) => X.assume(c2, which === 'R' ? 'c < x' : 'c - r < x', (h1, c3) => X.assume(c3, which === 'R' ? 'x < c + r' : 'x < c', (h2, c4) => {
        const ab = use(which === 'R' ? 'RightAbs' : 'LeftAbs', ['x', 'c', 'r'], c4, [hx, cr, rr, h1, h2]);
        return X.tc(c4, [X.inst(X.tc(c4, [hr], NB('c', 'r', 'x in dom(f)')), ['x']), hx, ab], 'x in dom(f)');
      }))), 'x');
      const body = which === 'R' ? RN : LN;
      return X.tc(c1, [X.inst(X.defAx(which === 'R' ? 'RNbhd' : 'LNbhd'), ['f', 'c']), X.exI(X.tc(c1, [hr, all], `r in Real & 0 < r & ${body}`), 'r', `r in Real & 0 < r & ${body}`, 'r')], `${which}Nbhd(f,c)`);
    }, k);
    const epsPart = (which) => X.gen(X.assume(k, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => X.exE(use('FLimE', ['f', 'c', 'al', 'eps'], c2, [hf, he, hp]), 'de', (hd, cd) => {
      const der = X.tc(cd, [hd], 'de in Real');
      const fa = X.tc(cd, [hd], 'all x. (x in dom(f) -> 0 < abs(x - c) -> abs(x - c) < de -> abs(f[x] - al) < eps)');
      const all = X.gen(X.assume(cd, 'x in dom(f)', (hx, d1) => X.assume(d1, which === 'R' ? 'c < x' : 'c - de < x', (h1, d2) => X.assume(d2, which === 'R' ? 'x < c + de' : 'x < c', (h2, d3) => {
        const xr = use('RFnDom', ['f', 'x'], d3, [rf, hx]);
        const ab = use(which === 'R' ? 'RightAbs' : 'LeftAbs', ['x', 'c', 'de'], d3, [xr, cr, der, h1, h2]);
        return X.tc(d3, [X.inst(fa, ['x']), hx, ab], 'abs(f[x] - al) < eps');
      }))), 'x');
      const G = (which === 'R' ? RE : LE)('eps').replace(/^ex de\. \(/, '').replace(/\)$/, '');
      return X.exI(X.tc(cd, [hd, all], G), 'de', G, 'de');
    }, c2))), 'eps');
    return X.tc(k, [dR, dL, rf, cr, ar, side('R'), side('L'), epsPart('R'), epsPart('L')], 'FLimR(f,c,al) & FLimL(f,c,al)');
  });
  const bw = X.assume([], 'FLimR(f,c,al) & FLimL(f,c,al)', (h, k) => {
    const rf = X.tc(k, [h, dR], 'RFn(f)'), cr = X.tc(k, [h, dR], 'c in Real'), ar = X.tc(k, [h, dR], 'al in Real');
    const rn = X.tc(k, [h, dR, X.inst(X.defAx('RNbhd'), ['f', 'c'])], `ex r. (r in Real & 0 < r & ${RN})`);
    const ln = X.tc(k, [h, dL, X.inst(X.defAx('LNbhd'), ['f', 'c'])], `ex r. (r in Real & 0 < r & ${LN})`);
    const reps = X.tc(k, [h, dR], `all eps. (eps in Real -> 0 < eps -> ${RE('eps')})`);
    const leps = X.tc(k, [h, dL], `all eps. (eps in Real -> 0 < eps -> ${LE('eps')})`);
    // 2つの半径の小さい方で場合分け
    const both = (c0, r1line, r2line, name1, name2, condR, condL, goalX, mkGoal) => null;
    const pn = X.exE(rn, 'r1', (h1, c1) => X.exE(ln, 'r2', (h2, c2) => {
      const r1 = X.tc(c2, [h1], 'r1 in Real'), r2 = X.tc(c2, [h2], 'r2 in Real');
      return X.exE(use('MinPos', ['r1', 'r2'], c2, [r1, r2, X.tc(c2, [h1], '0 < r1'), X.tc(c2, [h2], '0 < r2')]), 'd', (hd, cd) => {
        const dr = X.tc(cd, [hd], 'd in Real');
        const all = X.gen(X.assume(cd, 'x in Real', (hx, d1) => X.assume(d1, '0 < abs(x - c)', (hp, d2) => X.assume(d2, 'abs(x - c) < d', (hl, d3) => {
          const sides = use('NeSides', ['x', 'c'], d3, [hx, cr, hp]);
          const lft = X.assume(d3, 'x < c', (hs, d4) => {
            const l = use('SideL', ['x', 'c', 'r2'], d4, [hx, cr, r2, hs, use('LtLeTrans', ['abs(x - c)', 'd', 'r2'], d4, [hl, X.tc(d4, [hd], 'd <= r2')])]);
            return X.tc(d4, [X.inst(X.tc(d4, [h2], LN.replace(/\br\b/g, 'r2')), ['x']), hx, l, hs], 'x in dom(f)');
          });
          const rgt = X.assume(d3, 'c < x', (hs, d4) => {
            const l = use('SideR', ['x', 'c', 'r1'], d4, [hx, cr, r1, hs, use('LtLeTrans', ['abs(x - c)', 'd', 'r1'], d4, [hl, X.tc(d4, [hd], 'd <= r1')])]);
            return X.tc(d4, [X.inst(X.tc(d4, [h1], RN.replace(/\br\b/g, 'r1')), ['x']), hx, hs, l], 'x in dom(f)');
          });
          return X.tc(d3, [sides, lft, rgt], 'x in dom(f)');
        }))), 'x');
        return X.tc(cd, [PN('f', 'c'), X.exI(X.tc(cd, [hd, all], `d in Real & 0 < d & ${NB('c', 'd', 'x in dom(f)')}`), 'r', `r in Real & 0 < r & ${NB('c', 'r', 'x in dom(f)')}`, 'd')], 'PNbhd(f,c)');
      }, c2);
    }, c1), k);
    const eps = X.gen(X.assume(k, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) =>
      X.exE(X.tc(c2, [X.inst(reps, ['eps']), he, hp], RE('eps')), 'd1', (q1, e1) => X.exE(X.tc(e1, [X.inst(leps, ['eps']), he, hp], LE('eps')), 'd2', (q2, e2) => {
        const d1r = X.tc(e2, [q1], 'd1 in Real'), d2r = X.tc(e2, [q2], 'd2 in Real');
        return X.exE(use('MinPos', ['d1', 'd2'], e2, [d1r, d2r, X.tc(e2, [q1], '0 < d1'), X.tc(e2, [q2], '0 < d2')]), 'de', (hd, cd) => {
          const all = X.gen(X.assume(cd, 'x in dom(f)', (hx, d1) => X.assume(d1, '0 < abs(x - c)', (hpp, d2) => X.assume(d2, 'abs(x - c) < de', (hl, d3) => {
            const xr = use('RFnDom', ['f', 'x'], d3, [rf, hx]);
            const sides = use('NeSides', ['x', 'c'], d3, [xr, cr, hpp]);
            const lft = X.assume(d3, 'x < c', (hs, d4) => {
              const l = use('SideL', ['x', 'c', 'd2'], d4, [xr, cr, d2r, hs, use('LtLeTrans', ['abs(x - c)', 'de', 'd2'], d4, [hl, X.tc(d4, [hd], 'de <= d2')])]);
              return X.tc(d4, [X.inst(X.tc(d4, [q2], 'all x. (x in dom(f) -> c - d2 < x -> x < c -> abs(f[x] - al) < eps)'), ['x']), hx, l, hs], 'abs(f[x] - al) < eps');
            });
            const rgt = X.assume(d3, 'c < x', (hs, d4) => {
              const l = use('SideR', ['x', 'c', 'd1'], d4, [xr, cr, d1r, hs, use('LtLeTrans', ['abs(x - c)', 'de', 'd1'], d4, [hl, X.tc(d4, [hd], 'de <= d1')])]);
              return X.tc(d4, [X.inst(X.tc(d4, [q1], 'all x. (x in dom(f) -> c < x -> x < c + d1 -> abs(f[x] - al) < eps)'), ['x']), hx, hs, l], 'abs(f[x] - al) < eps');
            });
            return X.tc(d3, [sides, lft, rgt], 'abs(f[x] - al) < eps');
          }))), 'x');
          const G = 'de in Real & 0 < de & all x. (x in dom(f) -> 0 < abs(x - c) -> abs(x - c) < de -> abs(f[x] - al) < eps)';
          return X.exI(X.tc(cd, [hd, all], G), 'de', G, 'de');
        }, e2);
      }, e1), c2))), 'eps');
    return X.tc(k, [X.inst(X.defAx('FLim'), ['f', 'c', 'al']), rf, cr, ar, pn, eps], 'FLim(f,c,al)');
  });
  return X.tc([], [fw, bw], 'FLim(f,c,al) <-> FLimR(f,c,al) & FLimL(f,c,al)');
})(), ['f', 'c', 'al']));

module.exports = { ccInst, EPS, EPSf, SEQH };
