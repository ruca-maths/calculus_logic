'use strict';
// テキスト第4章 2節: 連続性 (定義2.1, 2.2, 2.8, 定理2.3, 2.4, 2.6, 2.7, 2.9, 2.10)
const K = require('./kit');
const { X, C, prove, intro, use, calc, mem, P, T } = K;
const { def, fthm } = require('./theory');
const L = require('./lang');
const { convIntro, tailIntro, tailAt } = require('./p_seq');
const { ccInst } = require('./p_fun');

for (const [n, ar] of [['ContIn', 3], ['Cont', 2], ['RCont', 2], ['LCont', 2], ['ContOn', 2], ['UC', 2]]) L.defPred(n, ar, a => `\\mathrm{${n}}(${a.join(',')})`);
L.defFunc('cint', 2, a => `[${a[0]},${a[1]}]`);

const CE = (A, c, e) => `ex de. (de in Real & 0 < de & all x. (x in ${A} -> abs(x - ${c}) < de -> abs(f[x] - f[${c}]) < ${e}))`;
def('ContIn', `all f. all A. all c. (ContIn(f,A,c) <-> RFn(f) & A sub dom(f) & c in A & all eps. (eps in Real -> 0 < eps -> ${CE('A', 'c', 'eps')}))`, 'DefContIn');
def('Cont', 'all f. all c. (Cont(f,c) <-> ContIn(f, dom(f), c))', 'DefCont');
def('ContOn', 'all f. all A. (ContOn(f,A) <-> RFn(f) & A sub dom(f) & all c. (c in A -> ContIn(f,A,c)))', 'DefContOn');
def('RCont', 'all f. all c. (RCont(f,c) <-> RFn(f) & c in dom(f) & all eps. (eps in Real -> 0 < eps -> ex de. (de in Real & 0 < de & all x. (x in dom(f) -> c <= x -> x < c + de -> abs(f[x] - f[c]) < eps))))', 'DefRCont');
def('LCont', 'all f. all c. (LCont(f,c) <-> RFn(f) & c in dom(f) & all eps. (eps in Real -> 0 < eps -> ex de. (de in Real & 0 < de & all x. (x in dom(f) -> c - de < x -> x <= c -> abs(f[x] - f[c]) < eps))))', 'DefLCont');
def('cint', 'all a. all b. all x. (x in cint(a,b) <-> x in Real & a <= x & x <= b)', 'Def{$[a,b]$}');
fthm('CompDom', 'all g. all f. all x. (RFn(g) -> RFn(f) -> x in dom(f) -> f[x] in dom(g) -> x in dom(comp(g,f)))', '[S23]', '関数の合成');

const cinDef = (f, A, c) => X.inst(X.defAx('ContIn'), [f, A, c]);
const subE = (c, Aline, A, B, x, hx) => use('SubElem', [A, B, x], c, [Aline, hx]);

// ---------------- 連続性の数列による特徴付け (Heine) ----------------
prove('ContInSeq', 'all f. all A. all c. all a. (ContIn(f,A,c) -> Seq(a) -> (all n. (n in Nat -> a[n] in A)) -> Conv(a,c) -> Conv(compseq(f,a), f[c]))', '[G1]', () => X.genAll(
  X.assume([], 'ContIn(f,A,c)', (hc, k1) => X.assume(k1, 'Seq(a)', (sa, k2) => X.assume(k2, 'all n. (n in Nat -> a[n] in A)', (hA, k3) => X.assume(k3, 'Conv(a,c)', (ha, k) => {
    const rf = X.tc(k, [hc, cinDef('f', 'A', 'c')], 'RFn(f)'), As = X.tc(k, [hc, cinDef('f', 'A', 'c')], 'A sub dom(f)'), cA = X.tc(k, [hc, cinDef('f', 'A', 'c')], 'c in A');
    const eps = X.tc(k, [hc, cinDef('f', 'A', 'c')], `all eps. (eps in Real -> 0 < eps -> ${CE('A', 'c', 'eps')})`);
    const dom1 = X.gen(X.assume(k, 'n in Nat', (hn, cn) => subE(cn, As, 'A', 'dom(f)', 'a[n]', X.tc(cn, [X.inst(hA, ['n']), hn], 'a[n] in A'))), 'n');
    const cs = use('CompSeq', ['f', 'a'], k, [rf, sa, dom1]);
    const fc = mem(k, 'f[c]', [rf, subE(k, As, 'A', 'dom(f)', 'c', cA)]);
    return convIntro(k, 'compseq(f,a)', 'f[c]', X.tc(k, [cs], 'Seq(compseq(f,a))'), fc, (c2, he, hp) =>
      X.exE(X.tc(c2, [X.inst(eps, ['eps']), he, hp], CE('A', 'c', 'eps')), 'de', (hd, cd) =>
        X.exE(use('ConvE', ['a', 'c', 'de'], cd, [ha, X.tc(cd, [hd], 'de in Real'), X.tc(cd, [hd], '0 < de')]), 'N', (hN, cN) =>
          tailIntro(cN, 'N', X.tc(cN, [hN], 'N in Nat'), n => `abs(compseq(f,a)[${n}] - f[c]) < eps`, (cl, hn, hl) => {
            const l = tailAt(cl, hN, 'N', n => `abs(a[${n}] - c) < de`, 'n', hn, hl);
            const r = X.tc(cl, [X.inst(X.tc(cl, [hd], 'all x. (x in A -> abs(x - c) < de -> abs(f[x] - f[c]) < eps)'), ['a[n]']), X.inst(hA, ['n']), hn, l], 'abs(f[a[n]] - f[c]) < eps');
            const v = X.tc(cl, [X.inst(X.tc(cl, [cs], 'all n. (n in Nat -> compseq(f,a)[n] = f[a[n]])'), ['n']), hn], 'compseq(f,a)[n] = f[a[n]]');
            return X.rw(X.sym(v), r, 'abs(compseq(f,a)[n] - f[c]) < eps', cl);
          }), cd)));
  })))), ['f', 'A', 'c', 'a']));

const SEQC = (f, A, c) => `(all a. (Seq(a) -> (all n. (n in Nat -> a[n] in ${A})) -> Conv(a,${c}) -> Conv(compseq(${f},a), ${f}[${c}])))`;
const PSIc = 'x in A & abs(x - c) < iota(k)^-1 & ~ abs(f[x] - f[c]) < e0';
const ccC = ccInst(PSIc);
prove('ContSeqInv', `all f. all A. all c. (RFn(f) -> A sub dom(f) -> c in A -> ${SEQC('f', 'A', 'c')} -> ContIn(f,A,c))`, '[G2]', () => X.genAll(
  X.assume([], 'RFn(f)', (rf, k1) => X.assume(k1, 'A sub dom(f)', (As, k2) => X.assume(k2, 'c in A', (cA, k3) => X.assume(k3, SEQC('f', 'A', 'c'), (H, k) => {
    const EPSs = `all eps. (eps in Real -> 0 < eps -> ${CE('A', 'c', 'eps')})`;
    const fc = mem(k, 'f[c]', [rf, subE(k, As, 'A', 'dom(f)', 'c', cA)]);
    const cr = use('RFnDom', ['f', 'c'], k, [rf, subE(k, As, 'A', 'dom(f)', 'c', cA)]);
    const eps = X.raa(k, EPSs, (hn, c2) => [X.exE(X.notAllToEx(hn), 'e0', (he0, c3) => {
      const e0r = X.tc(c3, [he0], 'e0 in Real'), e0p = X.tc(c3, [he0], '0 < e0');
      const never = X.tc(c3, [he0], 'all de. ~(de in Real & 0 < de & all x. (x in A -> abs(x - c) < de -> abs(f[x] - f[c]) < e0))');
      const pre = X.gen(X.assume(c3, 'k in Nat', (hk, ck) => {
        const ip = use('IotaPos', ['k'], ck, [hk]);
        const kz = X.neSym(use('LtNe', ['0', 'iota(k)'], ck, [ip]));
        const d = 'iota(k)^-1';
        const na = X.tc(ck, [X.inst(never, [d]), mem(ck, d, [hk, kz]), use('InvPos', ['iota(k)'], ck, [hk, ip])], `~ all x. (x in A -> abs(x - c) < ${d} -> abs(f[x] - f[c]) < e0)`);
        return X.exE(X.notAllToEx(na), 'x', (hx, cx) => {
          const xA = X.tc(cx, [hx], 'x in A');
          const xr = use('RFnDom', ['f', 'x'], cx, [rf, subE(cx, As, 'A', 'dom(f)', 'x', xA)]);
          return X.exI(X.tc(cx, [hx, xr], `x in Real & (${PSIc})`), 'x', `x in Real & (${PSIc})`, 'x');
        }, ck);
      }), 'k');
      return X.exE(ccC(c3, [pre]), 'a', (ha, ca) => {
        const sa = X.tc(ca, [ha], 'Seq(a)');
        const pa = X.tc(ca, [ha], `all k. (k in Nat -> ${PSIc.replace(/\bx\b/g, 'a[k]')})`);
        const at = (cc, n, hn) => X.tc(cc, [X.inst(pa, [n]), hn], PSIc.replace(/\bx\b/g, `a[${n}]`).replace(/\bk\b/g, n));
        const inA = X.gen(X.assume(ca, 'n in Nat', (hn, cn) => X.tc(cn, [at(cn, 'n', hn)], 'a[n] in A')), 'n');
        const conv = convIntro(ca, 'a', 'c', sa, cr, (c4, he, hp) => X.exE(use('ArchInv', ['eps'], c4, [he, hp]), 'K', (hK, cK) => {
          const kn = X.tc(cK, [hK], 'K in Nat');
          return tailIntro(cK, 'K', kn, n => `abs(a[${n}] - c) < eps`, (cl, hn, hl) => {
            const l = use('LtLeTrans', ['abs(a[n] - c)', 'iota(n)^-1', 'iota(K)^-1'], cl, [X.tc(cl, [at(cl, 'n', hn)], 'abs(a[n] - c) < iota(n)^-1'), use('IotaInvMono', ['K', 'n'], cl, [kn, hn, hl])]);
            return use('LtTrans', ['abs(a[n] - c)', 'iota(K)^-1', 'eps'], cl, [l, X.tc(cl, [hK], 'iota(K)^-1 < eps')]);
          });
        }));
        const fcv = X.tc(ca, [X.inst(H, ['a']), sa, inA, conv], 'Conv(compseq(f,a), f[c])');
        const dom1 = X.gen(X.assume(ca, 'n in Nat', (hn, cn) => subE(cn, As, 'A', 'dom(f)', 'a[n]', X.tc(cn, [X.inst(inA, ['n']), hn], 'a[n] in A'))), 'n');
        const cs = use('CompSeq', ['f', 'a'], ca, [rf, sa, dom1]);
        return X.exE(use('ConvE', ['compseq(f,a)', 'f[c]', 'e0'], ca, [fcv, e0r, e0p]), 'N', (hN, cN) => {
          const nN = X.tc(cN, [hN], 'N in Nat');
          const l = tailAt(cN, hN, 'N', n => `abs(compseq(f,a)[${n}] - f[c]) < e0`, 'N', nN, X.tc(cN, [X.refl('N')], 'N <= N'));
          const v = X.tc(cN, [X.inst(X.tc(cN, [cs], 'all n. (n in Nat -> compseq(f,a)[n] = f[a[n]])'), ['N']), nN], 'compseq(f,a)[N] = f[a[N]]');
          return X.tc(cN, [X.rw(v, l, 'abs(f[a[N]] - f[c]) < e0', cN), at(cN, 'N', nN)], '0 < 0');
        }, ca);
      }, c3);
    }, c2), X.inst(X.thm('LtIrrefl'), ['0'])]);
    return X.tc(k, [cinDef('f', 'A', 'c'), rf, As, cA, eps], 'ContIn(f,A,c)');
  })))), ['f', 'A', 'c']));

// 部分集合への制限
prove('ContInSub', 'all f. all A. all B. all c. (ContIn(f,A,c) -> B sub A -> c in B -> ContIn(f,B,c))', '[G3]', () => X.genAll(
  X.assume([], 'ContIn(f,A,c)', (hc, k1) => X.assume(k1, 'B sub A', (hB, k2) => X.assume(k2, 'c in B', (cB, k) => {
    const rf = X.tc(k, [hc, cinDef('f', 'A', 'c')], 'RFn(f)'), As = X.tc(k, [hc, cinDef('f', 'A', 'c')], 'A sub dom(f)');
    const Bs = X.tc(k, [X.inst(X.defAx('sub'), ['B', 'dom(f)']), X.gen(X.assume(k, 'u in B', (hu, cu) => subE(cu, As, 'A', 'dom(f)', 'u', subE(cu, hB, 'B', 'A', 'u', hu))), 'u')], 'B sub dom(f)');
    const eps = X.gen(X.assume(k, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) =>
      X.exE(X.tc(c2, [X.inst(X.tc(c2, [hc, cinDef('f', 'A', 'c')], `all eps. (eps in Real -> 0 < eps -> ${CE('A', 'c', 'eps')})`), ['eps']), he, hp], CE('A', 'c', 'eps')), 'de', (hd, cd) => {
        const all = X.gen(X.assume(cd, 'x in B', (hx, d1) => X.assume(d1, 'abs(x - c) < de', (hl, d2) =>
          X.tc(d2, [X.inst(X.tc(d2, [hd], 'all x. (x in A -> abs(x - c) < de -> abs(f[x] - f[c]) < eps)'), ['x']), subE(d2, hB, 'B', 'A', 'x', hx), hl], 'abs(f[x] - f[c]) < eps'))), 'x');
        const G = CE('B', 'c', 'eps').replace(/^ex de\. \(/, '').replace(/\)$/, '');
        return X.exI(X.tc(cd, [hd, all], G), 'de', G, 'de');
      }, c2))), 'eps');
    return X.tc(k, [cinDef('f', 'B', 'c'), rf, Bs, cB, eps], 'ContIn(f,B,c)');
  }))), ['f', 'A', 'B', 'c']));

// ---------------- 定理 2.3 / 2.9: 和・定数倍・積・商・絶対値 ----------------
//  ContIn(f,A,c) (, ContIn(g,A,c)) から ContIn(F,A,c) — 数列の極限の定理に帰着する
function contOp(name, label, vars, hyps, F, FThm, FArgs, domCond, valExpr, seqStep) {
  prove(name, `${vars.map(v => 'all ' + v + '. ').join('')}(${hyps.join(' -> ')} -> ContIn(${F}, A, c))`, label, () => {
    const rec = (i, ctx, hs) => i < hyps.length ? X.assume(ctx, hyps[i], (h, c) => rec(i + 1, c, [...hs, h])) : (() => {
      const k = ctx;
      const hf = hs.find(h => h.phi.k === 'rel' && h.phi.r === 'ContIn' && h.phi.a[0].n === 'f');
      const hg = hs.find(h => h.phi.k === 'rel' && h.phi.r === 'ContIn' && h.phi.a[0].n === 'g');
      const rf = X.tc(k, [hf, cinDef('f', 'A', 'c')], 'RFn(f)'), Af = X.tc(k, [hf, cinDef('f', 'A', 'c')], 'A sub dom(f)'), cA = X.tc(k, [hf, cinDef('f', 'A', 'c')], 'c in A');
      const rg = hg ? X.tc(k, [hg, cinDef('g', 'A', 'c')], 'RFn(g)') : null, Ag = hg ? X.tc(k, [hg, cinDef('g', 'A', 'c')], 'A sub dom(g)') : null;
      const FL = use(FThm, FArgs, k, [...hs, rf, ...(rg ? [rg] : [])]);
      const rF = X.tc(k, [FL], `RFn(${F})`);
      const domIff = X.tc(k, [FL], `all x. (x in dom(${F}) <-> ${domCond('x')})`);
      const valF = X.tc(k, [FL], `all x. (x in dom(${F}) -> ${F}[x] = ${valExpr('x')})`);
      const extra = hs.filter(h => h.phi.k === 'all');
      const inDom = (cc, x, hxA) => {
        const parts = [subE(cc, Af, 'A', 'dom(f)', x, hxA)];
        if (Ag) parts.push(subE(cc, Ag, 'A', 'dom(g)', x, hxA));
        const ex = extra.map(h => X.tc(cc, [X.inst(h, [x]), hxA], C.subst(h.phi.a.b, h.phi.v, T(x))));
        return X.tc(cc, [...parts, ...ex, X.inst(domIff, [x])], `${x} in dom(${F})`);
      };
      const AF = X.tc(k, [X.inst(X.defAx('sub'), ['A', `dom(${F})`]), X.gen(X.assume(k, 'u in A', (hu, cu) => inDom(cu, 'u', hu)), 'u')], `A sub dom(${F})`);
      const sq = X.gen(X.assume(k, 'Seq(a)', (sa, c1) => X.assume(c1, 'all n. (n in Nat -> a[n] in A)', (hA, c2) => X.assume(c2, 'Conv(a,c)', (ha, c3) => {
        const cf = use('ContInSeq', ['f', 'A', 'c', 'a'], c3, [hf, sa, hA, ha]);
        const cg = hg ? use('ContInSeq', ['g', 'A', 'c', 'a'], c3, [hg, sa, hA, ha]) : null;
        const aA = (cn, hn) => X.tc(cn, [X.inst(hA, ['n']), hn], 'a[n] in A');
        const csMemo = {};
        const csLine = (h, rh, Ah) => csMemo[h] ?? (csMemo[h] = (() => {
          const dom1 = X.gen(X.assume(c3, 'n in Nat', (hm, cm) => subE(cm, Ah, 'A', `dom(${h})`, 'a[n]', X.tc(cm, [X.inst(hA, ['n']), hm], 'a[n] in A'))), 'n');
          return use('CompSeq', [h, 'a'], c3, [rh, sa, dom1]);
        })());
        const cval = (cn, hn, h, rh, Ah) => X.tc(cn, [X.inst(X.tc(cn, [csLine(h, rh, Ah)], `all n. (n in Nat -> compseq(${h},a)[n] = ${h}[a[n]])`), ['n']), hn], `compseq(${h},a)[n] = ${h}[a[n]]`);
        csLine('f', rf, Af); if (hg) csLine('g', rg, Ag);
        const { other, lim, ovals } = seqStep(c3, cf, cg, hs);
        const domF = X.gen(X.assume(c3, 'n in Nat', (hn, cn) => inDom(cn, 'a[n]', aA(cn, hn))), 'n');
        const csF = use('CompSeq', [F, 'a'], c3, [rF, sa, domF]);
        const eq = X.gen(X.assume(c3, 'n in Nat', (hn, cn) => {
          const v = X.tc(cn, [X.inst(X.tc(cn, [csF], `all n. (n in Nat -> compseq(${F},a)[n] = ${F}[a[n]])`), ['n']), hn], `compseq(${F},a)[n] = ${F}[a[n]]`);
          const v2 = X.tc(cn, [X.inst(valF, ['a[n]']), X.inst(domF, ['n']), hn], `${F}[a[n]] = ${valExpr('a[n]')}`);
          const o = ovals(cn, hn, cval(cn, hn, 'f', rf, Af), hg ? cval(cn, hn, 'g', rg, Ag) : null);
          return X.sym(X.trans(X.trans(v, v2, cn), X.sym(o), cn));
        }), 'n');
        const c1v = use('ConvExt', [other, `compseq(${F},a)`, valExpr('c')], c3, [X.tc(c3, [csF], `Seq(compseq(${F},a))`), eq, lim]);
        const vc = X.tc(c3, [X.inst(valF, ['c']), inDom(c3, 'c', cA)], `${F}[c] = ${valExpr('c')}`);
        return X.rw(X.sym(vc), c1v, `Conv(compseq(${F},a), ${F}[c])`, c3);
      }))), 'a');
      return use('ContSeqInv', [F, 'A', 'c'], k, [rF, AF, cA, sq]);
    })();
    return X.genAll(rec(0, [], []), vars);
  });
}
const nval = (cn, line, seq, rhs, hn) => X.tc(cn, [X.inst(X.tc(cn, [line], `all n. (n in Nat -> ${seq}[n] = ${rhs})`), ['n']), hn], `${seq}[n] = ${rhs}`);

contOp('ContInAdd', '定理2.3(和)', ['f', 'g', 'A', 'c'], ['ContIn(f,A,c)', 'ContIn(g,A,c)'], 'fadd(f,g)', 'FAdd', ['f', 'g'], x => `${x} in dom(f) & ${x} in dom(g)`, x => `f[${x}] + g[${x}]`, (c3, cf, cg) => {
  const sf = use('ConvSeq', ['compseq(f,a)', 'f[c]'], c3, [cf]), sg = use('ConvSeq', ['compseq(g,a)', 'g[c]'], c3, [cg]);
  const S = 'oplus(compseq(f,a), compseq(g,a))';
  const op = use('Oplus', ['compseq(f,a)', 'compseq(g,a)'], c3, [sf, sg]);
  return { other: S, lim: use('LimSum', ['compseq(f,a)', 'f[c]', 'compseq(g,a)', 'g[c]'], c3, [cf, cg]),
    ovals: (cn, hn, vf, vg) => calc(cn, `${S}[n]`, [['compseq(f,a)[n] + compseq(g,a)[n]', nval(cn, op, S, 'compseq(f,a)[n] + compseq(g,a)[n]', hn)], ['f[a[n]] + compseq(g,a)[n]', vf], ['f[a[n]] + g[a[n]]', vg]]) };
});
contOp('ContInMul', '定理2.3(積)', ['f', 'g', 'A', 'c'], ['ContIn(f,A,c)', 'ContIn(g,A,c)'], 'fmul(f,g)', 'FMul', ['f', 'g'], x => `${x} in dom(f) & ${x} in dom(g)`, x => `f[${x}] * g[${x}]`, (c3, cf, cg) => {
  const sf = use('ConvSeq', ['compseq(f,a)', 'f[c]'], c3, [cf]), sg = use('ConvSeq', ['compseq(g,a)', 'g[c]'], c3, [cg]);
  const S = 'otimes(compseq(f,a), compseq(g,a))';
  const op = use('Otimes', ['compseq(f,a)', 'compseq(g,a)'], c3, [sf, sg]);
  return { other: S, lim: use('LimProd', ['compseq(f,a)', 'f[c]', 'compseq(g,a)', 'g[c]'], c3, [cf, cg]),
    ovals: (cn, hn, vf, vg) => calc(cn, `${S}[n]`, [['compseq(f,a)[n] * compseq(g,a)[n]', nval(cn, op, S, 'compseq(f,a)[n] * compseq(g,a)[n]', hn)], ['f[a[n]] * compseq(g,a)[n]', vf], ['f[a[n]] * g[a[n]]', vg]]) };
});
contOp('ContInScal', '定理2.3(定数倍)', ['l', 'f', 'A', 'c'], ['l in Real', 'ContIn(f,A,c)'], 'fscal(l,f)', 'FScal', ['l', 'f'], x => `${x} in dom(f)`, x => `l * f[${x}]`, (c3, cf, cg, hs) => {
  const sf = use('ConvSeq', ['compseq(f,a)', 'f[c]'], c3, [cf]);
  const S = 'odot(l, compseq(f,a))';
  const op = use('Odot', ['l', 'compseq(f,a)'], c3, [hs[0], sf]);
  return { other: S, lim: use('LimScalar', ['l', 'compseq(f,a)', 'f[c]'], c3, [hs[0], cf]),
    ovals: (cn, hn, vf) => calc(cn, `${S}[n]`, [['l * compseq(f,a)[n]', nval(cn, op, S, 'l * compseq(f,a)[n]', hn)], ['l * f[a[n]]', vf]]) };
});
contOp('ContInAbs', '定理2.3(絶対値)', ['f', 'A', 'c'], ['ContIn(f,A,c)'], 'fabs(f)', 'FAbs', ['f'], x => `${x} in dom(f)`, x => `abs(f[${x}])`, (c3, cf) => {
  const sf = use('ConvSeq', ['compseq(f,a)', 'f[c]'], c3, [cf]);
  const S = 'absq(compseq(f,a))';
  const op = use('AbsSeq', ['compseq(f,a)'], c3, [sf]);
  return { other: S, lim: use('LimAbs', ['compseq(f,a)', 'f[c]'], c3, [cf]),
    ovals: (cn, hn, vf) => calc(cn, `${S}[n]`, [['abs(compseq(f,a)[n])', nval(cn, op, S, 'abs(compseq(f,a)[n])', hn)], ['abs(f[a[n]])', vf]]) };
});
contOp('ContInDiv', '定理2.3(商)', ['f', 'g', 'A', 'c'], ['ContIn(f,A,c)', 'ContIn(g,A,c)', '(all x. (x in A -> g[x] != 0))'], 'fdiv(f,g)', 'FDiv', ['f', 'g'], x => `${x} in dom(f) & ${x} in dom(g) & g[${x}] != 0`, x => `f[${x}] * g[${x}]^-1`, (c3, cf, cg, hs) => {
  const sf = use('ConvSeq', ['compseq(f,a)', 'f[c]'], c3, [cf]), sg = use('ConvSeq', ['compseq(g,a)', 'g[c]'], c3, [cg]);
  const hz = hs[2];
  const hA = X.hyp(c3, 'all n. (n in Nat -> a[n] in A)');
  const rg = X.tc(c3, [hs[1], cinDef('g', 'A', 'c')], 'RFn(g)'), Ag = X.tc(c3, [hs[1], cinDef('g', 'A', 'c')], 'A sub dom(g)'), cA = X.tc(c3, [hs[1], cinDef('g', 'A', 'c')], 'c in A');
  const sa = X.hyp(c3, 'Seq(a)');
  const dom1 = X.gen(X.assume(c3, 'n in Nat', (hm, cm) => subE(cm, Ag, 'A', 'dom(g)', 'a[n]', X.tc(cm, [X.inst(hA, ['n']), hm], 'a[n] in A'))), 'n');
  const cs = use('CompSeq', ['g', 'a'], c3, [rg, sa, dom1]);
  const gnz = X.gen(X.assume(c3, 'n in Nat', (hn, cn) => {
    const v = X.tc(cn, [X.inst(X.tc(cn, [cs], 'all n. (n in Nat -> compseq(g,a)[n] = g[a[n]])'), ['n']), hn], 'compseq(g,a)[n] = g[a[n]]');
    return X.rw(X.sym(v), X.tc(cn, [X.inst(hz, ['a[n]']), X.inst(hA, ['n']), hn], 'g[a[n]] != 0'), 'compseq(g,a)[n] != 0', cn);
  }), 'n');
  const gc = X.tc(c3, [X.inst(hz, ['c']), cA], 'g[c] != 0');
  const rc = use('Recip', ['compseq(g,a)'], c3, [sg, gnz]);
  const S = 'otimes(compseq(f,a), recip(compseq(g,a)))';
  const op = use('Otimes', ['compseq(f,a)', 'recip(compseq(g,a))'], c3, [sf, X.tc(c3, [rc], 'Seq(recip(compseq(g,a)))')]);
  return { other: S, lim: use('LimQuot', ['compseq(f,a)', 'f[c]', 'compseq(g,a)', 'g[c]'], c3, [cf, cg, gc, gnz]),
    ovals: (cn, hn, vf, vg) => calc(cn, `${S}[n]`, [['compseq(f,a)[n] * recip(compseq(g,a))[n]', nval(cn, op, S, 'compseq(f,a)[n] * recip(compseq(g,a))[n]', hn)],
      ['compseq(f,a)[n] * compseq(g,a)[n]^-1', nval(cn, rc, 'recip(compseq(g,a))', 'compseq(g,a)[n]^-1', hn)], ['f[a[n]] * compseq(g,a)[n]^-1', vf], ['f[a[n]] * g[a[n]]^-1', vg]]) };
});

// ---------------- 定理 2.6 / 2.10: 合成関数の連続性 ----------------
prove('ContInComp', 'all f. all g. all A. all B. all c. (ContIn(f,A,c) -> ContIn(g,B,f[c]) -> (all x. (x in A -> f[x] in B)) -> ContIn(comp(g,f), A, c))', '定理2.6', () => X.genAll(
  X.assume([], 'ContIn(f,A,c)', (hf, k1) => X.assume(k1, 'ContIn(g,B,f[c])', (hg, k2) => X.assume(k2, 'all x. (x in A -> f[x] in B)', (hAB, k) => {
    const dF = cinDef('f', 'A', 'c'), dG = cinDef('g', 'B', 'f[c]');
    const rf = X.tc(k, [hf, dF], 'RFn(f)'), Af = X.tc(k, [hf, dF], 'A sub dom(f)'), cA = X.tc(k, [hf, dF], 'c in A');
    const rg = X.tc(k, [hg, dG], 'RFn(g)'), Bg = X.tc(k, [hg, dG], 'B sub dom(g)');
    const cf = use('CompFn', ['g', 'f'], k, [rg, rf]);
    const rc = X.tc(k, [cf], 'RFn(comp(g,f))');
    const cval = X.tc(k, [cf], 'all x. (x in dom(comp(g,f)) -> x in dom(f) & f[x] in dom(g) & comp(g,f)[x] = g[f[x]])');
    const inD = (cc, x, hx) => use('CompDom', ['g', 'f', x], cc, [rg, rf, subE(cc, Af, 'A', 'dom(f)', x, hx), subE(cc, Bg, 'B', 'dom(g)', `f[${x}]`, X.tc(cc, [X.inst(hAB, [x]), hx], `f[${x}] in B`))]);
    const vOf = (cc, x, hx) => X.tc(cc, [X.inst(cval, [x]), inD(cc, x, hx)], `comp(g,f)[${x}] = g[f[${x}]]`);
    const AC = X.tc(k, [X.inst(X.defAx('sub'), ['A', 'dom(comp(g,f))']), X.gen(X.assume(k, 'u in A', (hu, cu) => inD(cu, 'u', hu)), 'u')], 'A sub dom(comp(g,f))');
    const epsG = X.tc(k, [hg, dG], `all eps. (eps in Real -> 0 < eps -> ex de. (de in Real & 0 < de & all x. (x in B -> abs(x - f[c]) < de -> abs(g[x] - g[f[c]]) < eps)))`);
    const epsF = X.tc(k, [hf, dF], `all eps. (eps in Real -> 0 < eps -> ${CE('A', 'c', 'eps')})`);
    const eps = X.gen(X.assume(k, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) =>
      X.exE(X.tc(c2, [X.inst(epsG, ['eps']), he, hp], 'ex de. (de in Real & 0 < de & all x. (x in B -> abs(x - f[c]) < de -> abs(g[x] - g[f[c]]) < eps))'), 'd1', (h1, d1) =>
        X.exE(X.tc(d1, [X.inst(epsF, ['d1']), h1], CE('A', 'c', 'd1')), 'de', (h2, d2) => {
          const all = X.gen(X.assume(d2, 'x in A', (hx, e1) => X.assume(e1, 'abs(x - c) < de', (hl, e2) => {
            const l1 = X.tc(e2, [X.inst(X.tc(e2, [h2], 'all x. (x in A -> abs(x - c) < de -> abs(f[x] - f[c]) < d1)'), ['x']), hx, hl], 'abs(f[x] - f[c]) < d1');
            const l2 = X.tc(e2, [X.inst(X.tc(e2, [h1], 'all x. (x in B -> abs(x - f[c]) < d1 -> abs(g[x] - g[f[c]]) < eps)'), ['f[x]']), X.inst(hAB, ['x']), hx, l1], 'abs(g[f[x]] - g[f[c]]) < eps');
            return X.rw(X.sym(vOf(e2, 'c', cA)), X.rw(X.sym(vOf(e2, 'x', hx)), l2, 'abs(comp(g,f)[x] - g[f[c]]) < eps', e2), 'abs(comp(g,f)[x] - comp(g,f)[c]) < eps', e2);
          })), 'x');
          const G = 'de in Real & 0 < de & all x. (x in A -> abs(x - c) < de -> abs(comp(g,f)[x] - comp(g,f)[c]) < eps)';
          return X.exI(X.tc(d2, [h2, all], G), 'de', G, 'de');
        }, d1), c2))), 'eps');
    return X.tc(k, [cinDef('comp(g,f)', 'A', 'c'), rc, AC, cA, eps], 'ContIn(comp(g,f), A, c)');
  }))), ['f', 'g', 'A', 'B', 'c']));

// 区間上の連続関数 (定理 2.9, 2.10)
const coDef = (f, A) => X.inst(X.defAx('ContOn'), [f, A]);
prove('ContOnAdd', 'all f. all g. all A. (ContOn(f,A) -> ContOn(g,A) -> ContOn(fadd(f,g), A))', '定理2.9(和)', () => X.genAll(
  X.assume([], 'ContOn(f,A)', (hf, k1) => X.assume(k1, 'ContOn(g,A)', (hg, k) => {
    const rf = X.tc(k, [hf, coDef('f', 'A')], 'RFn(f)'), rg = X.tc(k, [hg, coDef('g', 'A')], 'RFn(g)');
    const FA = use('FAdd', ['f', 'g'], k, [rf, rg]);
    const all = X.gen(X.assume(k, 'c in A', (hc, cc) => use('ContInAdd', ['f', 'g', 'A', 'c'], cc, [X.tc(cc, [X.inst(X.tc(cc, [hf, coDef('f', 'A')], 'all c. (c in A -> ContIn(f,A,c))'), ['c']), hc], 'ContIn(f,A,c)'),
      X.tc(cc, [X.inst(X.tc(cc, [hg, coDef('g', 'A')], 'all c. (c in A -> ContIn(g,A,c))'), ['c']), hc], 'ContIn(g,A,c)')])), 'c');
    const Af = X.tc(k, [hf, coDef('f', 'A')], 'A sub dom(f)'), Ag = X.tc(k, [hg, coDef('g', 'A')], 'A sub dom(g)');
    const sub = X.tc(k, [X.inst(X.defAx('sub'), ['A', 'dom(fadd(f,g))']), X.gen(X.assume(k, 'u in A', (hu, cu) =>
      X.tc(cu, [subE(cu, Af, 'A', 'dom(f)', 'u', hu), subE(cu, Ag, 'A', 'dom(g)', 'u', hu), X.inst(X.tc(cu, [FA], 'all x. (x in dom(fadd(f,g)) <-> x in dom(f) & x in dom(g))'), ['u'])], 'u in dom(fadd(f,g))')), 'u')], 'A sub dom(fadd(f,g))');
    return X.tc(k, [coDef('fadd(f,g)', 'A'), X.tc(k, [FA], 'RFn(fadd(f,g))'), sub, all], 'ContOn(fadd(f,g), A)');
  })), ['f', 'g', 'A']));
prove('ContOnComp', 'all f. all g. all A. all B. (ContOn(f,A) -> ContOn(g,B) -> (all x. (x in A -> f[x] in B)) -> ContOn(comp(g,f), A))', '定理2.10', () => X.genAll(
  X.assume([], 'ContOn(f,A)', (hf, k1) => X.assume(k1, 'ContOn(g,B)', (hg, k2) => X.assume(k2, 'all x. (x in A -> f[x] in B)', (hAB, k) => {
    const cfa = c => X.tc(c[0], [X.inst(X.tc(c[0], [hf, coDef('f', 'A')], 'all c. (c in A -> ContIn(f,A,c))'), [c[1]]), c[2]], `ContIn(f,A,${c[1]})`);
    const all = X.gen(X.assume(k, 'c in A', (hc, cc) => {
      const gb = X.tc(cc, [X.inst(X.tc(cc, [hg, coDef('g', 'B')], 'all c. (c in B -> ContIn(g,B,c))'), ['f[c]']), X.inst(hAB, ['c']), hc], 'ContIn(g,B,f[c])');
      return use('ContInComp', ['f', 'g', 'A', 'B', 'c'], cc, [cfa([cc, 'c', hc]), gb, hAB]);
    }), 'c');
    const rf = X.tc(k, [hf, coDef('f', 'A')], 'RFn(f)'), rg = X.tc(k, [hg, coDef('g', 'B')], 'RFn(g)');
    const Af = X.tc(k, [hf, coDef('f', 'A')], 'A sub dom(f)'), Bg = X.tc(k, [hg, coDef('g', 'B')], 'B sub dom(g)');
    const sub = X.tc(k, [X.inst(X.defAx('sub'), ['A', 'dom(comp(g,f))']), X.gen(X.assume(k, 'u in A', (hu, cu) =>
      use('CompDom', ['g', 'f', 'u'], cu, [rg, rf, subE(cu, Af, 'A', 'dom(f)', 'u', hu), subE(cu, Bg, 'B', 'dom(g)', 'f[u]', X.tc(cu, [X.inst(hAB, ['u']), hu], 'f[u] in B'))])), 'u')], 'A sub dom(comp(g,f))');
    return X.tc(k, [coDef('comp(g,f)', 'A'), X.tc(k, [use('CompFn', ['g', 'f'], k, [rg, rf])], 'RFn(comp(g,f))'), sub, all], 'ContOn(comp(g,f), A)');
  }))), ['f', 'g', 'A', 'B']));

// ---------------- 定理 2.7: 符号の保存 ----------------
prove('ContPos', 'all f. all A. all c. (ContIn(f,A,c) -> 0 < f[c] -> ex de. (de in Real & 0 < de & all x. (x in A -> abs(x - c) < de -> f[c] * 2^-1 < f[x])))', '定理2.7', () => X.genAll(
  X.assume([], 'ContIn(f,A,c)', (hf, k1) => X.assume(k1, '0 < f[c]', (hp, k) => {
    const dF = cinDef('f', 'A', 'c');
    const rf = X.tc(k, [hf, dF], 'RFn(f)'), Af = X.tc(k, [hf, dF], 'A sub dom(f)'), cA = X.tc(k, [hf, dF], 'c in A');
    const fc = mem(k, 'f[c]', [rf, subE(k, Af, 'A', 'dom(f)', 'c', cA)]);
    const e = 'f[c] * 2^-1';
    const epsF = X.tc(k, [hf, dF], `all eps. (eps in Real -> 0 < eps -> ${CE('A', 'c', 'eps')})`);
    return X.exE(X.tc(k, [X.inst(epsF, [e]), mem(k, e, [fc]), use('HalfPos', ['f[c]'], k, [fc, hp])], CE('A', 'c', e)), 'de', (hd, cd) => {
      const all = X.gen(X.assume(cd, 'x in A', (hx, c1) => X.assume(c1, 'abs(x - c) < de', (hl, c2) => {
        const fx = mem(c2, 'f[x]', [rf, subE(c2, Af, 'A', 'dom(f)', 'x', hx)]);
        const l = X.tc(c2, [X.inst(X.tc(c2, [hd], `all x. (x in A -> abs(x - c) < de -> abs(f[x] - f[c]) < ${e})`), ['x']), hx, hl], `abs(f[x] - f[c]) < ${e}`);
        const lo = X.tc(c2, [use('AbsLt', ['f[x] - f[c]', e], c2, [fx, fc, l])], `-(${e}) < f[x] - f[c]`);
        // f(c) - e < f(x)  ⇐  -e < f(x) - f(c)
        const s = use('R14', [`-(${e})`, 'f[x] - f[c]', 'f[c]'], c2, [fx, fc, lo]);
        const lhs = calc(c2, `-(${e}) + f[c]`, [[`f[c] + -(${e})`, use('R3', [`-(${e})`, 'f[c]'], c2, [fc])], [`f[c] - ${e}`, X.sym(X.inst(X.defAx('minus'), ['f[c]', e]))],
          [`(${e} + ${e}) - ${e}`, X.sym(use('HalfSum', ['f[c]'], c2, [fc]))], [e, use('AddSub', [e, e], c2, [fc])]]);
        return X.rw(use('SubAdd', ['f[x]', 'f[c]'], c2, [fx, fc]), X.rw(lhs, s, `${e} < (f[x] - f[c]) + f[c]`, c2), `${e} < f[x]`, c2);
      })), 'x');
      const G = `de in Real & 0 < de & all x. (x in A -> abs(x - c) < de -> ${e} < f[x])`;
      return X.exI(X.tc(cd, [hd, all], G), 'de', G, 'de');
    }, k);
  })), ['f', 'A', 'c']));

module.exports = { CE, cinDef, subE, SEQC, coDef };
