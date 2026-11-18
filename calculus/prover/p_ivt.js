'use strict';
// テキスト第4章 2節: 定義2.1 の同値性, 中間値の定理(2.14), 最大値・最小値の定理(2.17)
const K = require('./kit');
const { X, C, prove, intro, use, calc, mem, P, T } = K;
const { CE, cinDef, subE, coDef } = require('./p_cont');
const { convIntro, tailIntro, tailAt } = require('./p_seq');
const { ccInst } = require('./p_fun');

// ---------------- 補題 ----------------
prove('HalfLt', 'all e. (e in Real -> 0 < e -> e * 2^-1 < e)', '[E39]', () => intro(['e'], ['0 < e'], (c, [h]) => {
  const hp = use('HalfPos', ['e'], c, [h]);
  return X.rw(use('HalfSum', ['e'], c), use('LtAddPos', ['e * 2^-1', 'e * 2^-1'], c, [hp]), 'e * 2^-1 < e', c);
}));
prove('SubNonneg', 'all x. all y. (x in Real -> y in Real -> x <= y -> 0 <= y - x)', '[E40]', () => intro(['x', 'y'], ['x <= y'], (c, [h]) => {
  const lt = X.assume(c, 'x < y', (h1, c1) => X.tc(c1, [use('SubPos', ['x', 'y'], c1, [h1])], '0 <= y - x'));
  const eq = X.assume(c, 'x = y', (h1, c1) => X.tc(c1, [X.sym(X.rw(h1, use('SubSelf', ['x'], c1), 'y - x = 0', c1))], '0 <= y - x'));
  return X.tc(c, [h, lt, eq], '0 <= y - x');
}));
prove('LeftAbsLe', 'all s. all x. all d. (s in Real -> x in Real -> d in Real -> s <= x -> x - d < s -> abs(s - x) < d)', '[E41]', () => intro(['s', 'x', 'd'], ['s <= x', 'x - d < s'], (c, [h1, h2]) => {
  const ab = X.trans(use('AbsSubComm', ['s', 'x'], c), use('AbsOfNonneg', ['x - s'], c, [use('SubNonneg', ['s', 'x'], c, [h1])]), c);
  const l1 = use('SubLtSwap', ['x', 'd', 's'], c, [h2]);   // -d < s - x
  const l2 = X.rw(use('SubNeg', ['x', 's'], c), X.rw(use('NegNeg', ['d'], c), use('NegLt', ['-d', 's - x'], c, [l1]), '-(s - x) < d', c), 'x - s < d', c);
  return X.rw(X.sym(ab), l2, 'abs(s - x) < d', c);
}));
prove('NegSubLt', 'all x. all m. all y. (x in Real -> m in Real -> y in Real -> -(x - m) < y - x -> m < y)', '[E42]', () => intro(['x', 'm', 'y'], ['-(x - m) < y - x'], (c, [h]) => {
  const l = X.rw(use('SubNeg', ['m', 'x'], c), h, 'm - x < y - x', c);
  const l2 = X.rw(X.inst(X.defAx('minus'), ['y', 'x']), X.rw(X.inst(X.defAx('minus'), ['m', 'x']), l, 'm + -x < y - x', c), 'm + -x < y + -x', c);
  return use('LtAddCancel', ['m', 'y', '-x'], c, [l2]);
}));
prove('SubRefl', 'all A. A sub A', '[E43]', () => X.gen(X.tc([], [X.inst(X.defAx('sub'), ['A', 'A']), X.gen(X.tc([], [], 'u in A -> u in A'), 'u')], 'A sub A'), 'A'));

// ---------------- 定義 2.1: 連続 ⇔ lim f(x) = f(c) ----------------
prove('ContLim', 'all f. all c. (PNbhd(f,c) -> c in dom(f) -> (Cont(f,c) <-> FLim(f,c,f[c])))', '命題(定義2.1)', () => X.genAll(
  X.assume([], 'PNbhd(f,c)', (pn, k1) => X.assume(k1, 'c in dom(f)', (cd, k) => {
    const dC = X.inst(X.defAx('Cont'), ['f', 'c']), dI = cinDef('f', 'dom(f)', 'c'), dL = X.inst(X.defAx('FLim'), ['f', 'c', 'f[c]']);
    const fw = X.assume(k, 'Cont(f,c)', (h, c0) => {
      const rf = X.tc(c0, [h, dC, dI], 'RFn(f)');
      const epsC = X.tc(c0, [h, dC, dI], `all eps. (eps in Real -> 0 < eps -> ${CE('dom(f)', 'c', 'eps')})`);
      const eps = X.gen(X.assume(c0, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => X.exE(X.tc(c2, [X.inst(epsC, ['eps']), he, hp], CE('dom(f)', 'c', 'eps')), 'de', (hd, cdd) => {
        const all = X.gen(X.assume(cdd, 'x in dom(f)', (hx, d1) => X.assume(d1, '0 < abs(x - c)', (h0, d2) => X.assume(d2, 'abs(x - c) < de', (hl, d3) =>
          X.tc(d3, [X.inst(X.tc(d3, [hd], 'all x. (x in dom(f) -> abs(x - c) < de -> abs(f[x] - f[c]) < eps)'), ['x']), hx, hl], 'abs(f[x] - f[c]) < eps')))), 'x');
        const G = 'de in Real & 0 < de & all x. (x in dom(f) -> 0 < abs(x - c) -> abs(x - c) < de -> abs(f[x] - f[c]) < eps)';
        return X.exI(X.tc(cdd, [hd, all], G), 'de', G, 'de');
      }, c2))), 'eps');
      return X.tc(c0, [dL, rf, use('RFnDom', ['f', 'c'], c0, [rf, cd]), mem(c0, 'f[c]', [rf, cd]), pn, eps], 'FLim(f,c,f[c])');
    });
    const bw = X.assume(k, 'FLim(f,c,f[c])', (h, c0) => {
      const rf = use('FLimRFn', ['f', 'c', 'f[c]'], c0, [h]), cr = use('FLimCR', ['f', 'c', 'f[c]'], c0, [h]);
      const eps = X.gen(X.assume(c0, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => X.exE(use('FLimE', ['f', 'c', 'f[c]', 'eps'], c2, [h, he, hp]), 'de', (hd, cdd) => {
        const fa = X.tc(cdd, [hd], 'all x. (x in dom(f) -> 0 < abs(x - c) -> abs(x - c) < de -> abs(f[x] - f[c]) < eps)');
        const all = X.gen(X.assume(cdd, 'x in dom(f)', (hx, d1) => X.assume(d1, 'abs(x - c) < de', (hl, d2) => {
          const xr = use('RFnDom', ['f', 'x'], d2, [rf, hx]);
          const same = X.assume(d2, 'x = c', (he2, d3) => {
            const z = calc(d3, 'abs(f[c] - f[c])', [['abs(0)', use('SubSelf', ['f[c]'], d3, [rf, cd])], ['0', use('AbsOfNonneg', ['0'], d3, [X.tc(d3, [X.refl('0')], '0 <= 0')])]]);
            return X.rw(X.sym(he2), X.rw(X.sym(z), hp, 'abs(f[c] - f[c]) < eps', d3), 'abs(f[x] - f[c]) < eps', d3);
          });
          const diff = X.assume(d2, 'x != c', (hn, d3) => {
            const p = use('AbsPos', ['x - c'], d3, [xr, cr, use('SubNeZero', ['x', 'c'], d3, [xr, cr, hn])]);
            return X.tc(d3, [X.inst(fa, ['x']), hx, p, hl], 'abs(f[x] - f[c]) < eps');
          });
          return X.tc(d2, [same, diff], 'abs(f[x] - f[c]) < eps');
        })), 'x');
        const G = 'de in Real & 0 < de & all x. (x in dom(f) -> abs(x - c) < de -> abs(f[x] - f[c]) < eps)';
        return X.exI(X.tc(cdd, [hd, all], G), 'de', G, 'de');
      }, c2))), 'eps');
      return X.tc(c0, [dC, dI, rf, X.inst(X.thm('SubRefl'), ['dom(f)']), cd, eps], 'Cont(f,c)');
    });
    return X.tc(k, [fw, bw], 'Cont(f,c) <-> FLim(f,c,f[c])');
  })), ['f', 'c']));

// ---------------- 定理 2.14: 中間値の定理 ----------------
const I = 'cint(a,b)';
const cdef = x => X.inst(X.defAx('cint'), ['a', 'b', x]);
const supDef = (s, E) => X.inst(X.defAx('IsSup'), [s, E]);
const ubDef = (b, E) => X.inst(X.defAx('UB'), [b, E]);
prove('IVT', 'all f. all a. all b. all mu. (ContOn(f, cint(a,b)) -> a in Real -> b in Real -> mu in Real -> a < b -> f[a] < mu -> mu < f[b] -> ex xi. (xi in Real & a < xi & xi < b & f[xi] = mu))', '定理2.14', () => X.genAll(
  X.assume([], `ContOn(f, ${I})`, (hco, k1) => X.assume(k1, 'a in Real', (ar, k2) => X.assume(k2, 'b in Real', (br, k3) => X.assume(k3, 'mu in Real', (mr, k4) =>
    X.assume(k4, 'a < b', (hab, k5) => X.assume(k5, 'f[a] < mu', (h1, k6) => X.assume(k6, 'mu < f[b]', (h2, k) => {
      const G = 'ex xi. (xi in Real & a < xi & xi < b & f[xi] = mu)';
      const rf = X.tc(k, [hco, coDef('f', I)], 'RFn(f)'), Isub = X.tc(k, [hco, coDef('f', I)], `${I} sub dom(f)`);
      const allC = X.tc(k, [hco, coDef('f', I)], `all c. (c in ${I} -> ContIn(f, ${I}, c))`);
      const aI = X.tc(k, [cdef('a'), ar, X.tc(k, [X.refl('a')], 'a <= a'), X.tc(k, [hab], 'a <= b')], `a in ${I}`);
      const sep = X.inst(X.axiom('Sep', 'all f. all mu. all A. ex W. all x. (x in W <-> x in A & f[x] < mu)'), ['f', 'mu', I]);
      return X.exE(sep, 'W', (hS, cS) => {
        const dS = t => X.inst(hS, [t]);
        const Sr = X.tc(cS, [X.inst(X.defAx('sub'), ['W', 'Real']), X.gen(X.assume(cS, 'u in W', (hu, cu) => X.tc(cu, [dS('u'), hu, cdef('u')], 'u in Real')), 'u')], 'W sub Real');
        const aS = X.tc(cS, [dS('a'), aI, h1], 'a in W');
        const ub = X.tc(cS, [ubDef('b', 'W'), br, X.gen(X.assume(cS, 'x in W', (hx, cx) => X.tc(cx, [dS('x'), hx, cdef('x')], 'x <= b')), 'x')], 'UB(b, W)');
        return X.exE(use('R16', ['W'], cS, [Sr, use('ExNonempty', ['W', 'a'], cS, [aS]), X.exI(ub, 'b', 'UB(b, W)', 'b')]), 'xi', (hx, cx) => {
          const xr = X.tc(cx, [hx, supDef('xi', 'W'), ubDef('xi', 'W')], 'xi in Real');
          const ubx = X.tc(cx, [hx, supDef('xi', 'W'), ubDef('xi', 'W')], 'all x. (x in W -> x <= xi)');
          const least = X.tc(cx, [hx, supDef('xi', 'W')], 'all w. (UB(w,W) -> xi <= w)');
          const axi = X.tc(cx, [X.inst(ubx, ['a']), aS], 'a <= xi');
          const xib = X.tc(cx, [X.inst(least, ['b']), ub], 'xi <= b');
          const xiI = X.tc(cx, [cdef('xi'), xr, axi, xib], `xi in ${I}`);
          const fxi = mem(cx, 'f[xi]', [rf, subE(cx, Isub, I, 'dom(f)', 'xi', xiI)]);
          const g = [ar, br, mr, xr, fxi];
          const epsC = X.tc(cx, [X.inst(allC, ['xi']), xiI, cinDef('f', I, 'xi')], `all eps. (eps in Real -> 0 < eps -> ${CE(I, 'xi', 'eps')})`);
          const near = (cc, e, he, hp) => X.tc(cc, [X.inst(epsC, [e]), he, hp], CE(I, 'xi', e));
          const fOf = (cc, x, hxI) => mem(cc, `f[${x}]`, [rf, subE(cc, Isub, I, 'dom(f)', x, hxI)]);
          // 場合1: f(ξ) < μ
          const case1 = X.assume(cx, 'f[xi] < mu', (hc1, c1) => {
            const e = 'mu - f[xi]';
            const ep = use('SubPos', ['f[xi]', 'mu'], c1, [...g, hc1]);
            const xne = X.raa(c1, 'xi != b', (hn, c2) => {
              const e2 = X.tc(c2, [hn], 'xi = b');
              const l = X.rw(e2, hc1, 'f[b] < mu', c2);
              return [use('LtTrans', ['mu', 'f[b]', 'mu'], c2, [h2, l]), X.inst(X.thm('LtIrrefl'), ['mu'])];
            });
            const xlb = X.tc(c1, [xib, xne], 'xi < b');
            return X.exE(near(c1, e, mem(c1, e, g), ep), 'de', (hd, cd) => {
              const der = X.tc(cd, [hd], 'de in Real'), dep = X.tc(cd, [hd], '0 < de');
              const h2d = 'de * 2^-1';
              return X.exE(use('MinPos', [h2d, 'b - xi'], cd, [...g, der, use('HalfPos', ['de'], cd, [der, dep]), use('SubPos', ['xi', 'b'], cd, [...g, xlb])]), 'd', (hdd, cdd) => {
                const dr = X.tc(cdd, [hdd], 'd in Real'), dp = X.tc(cdd, [hdd], '0 < d');
                const gg = [...g, der, dr];
                const x = 'xi + d';
                const xR = mem(cdd, x, gg);
                const ax = use('LeTrans', ['a', 'xi', x], cdd, [axi, use('LeAddNonneg', ['xi', 'd'], cdd, [...gg, X.tc(cdd, [dp], '0 <= d')])]);
                const xb0 = use('LeAddRight', ['d', 'b - xi', 'xi'], cdd, [...gg, X.tc(cdd, [hdd], 'd <= b - xi')]);
                const xb = X.rw(use('R3', ['d', 'xi'], cdd, gg), X.rw(use('SubAdd', ['b', 'xi'], cdd, gg), xb0, 'd + xi <= b', cdd), `${x} <= b`, cdd);
                const xI = X.tc(cdd, [cdef(x), xR, ax, xb], `${x} in ${I}`);
                const dist = calc(cdd, `abs(${x} - xi)`, [['abs((d + xi) - xi)', use('R3', ['xi', 'd'], cdd, gg)], ['abs(d)', use('AddSub', ['d', 'xi'], cdd, gg)], ['d', use('AbsOfNonneg', ['d'], cdd, [X.tc(cdd, [dp], '0 <= d')])]]);
                const dl = use('LeLtTrans', ['d', h2d, 'de'], cdd, [X.tc(cdd, [hdd], `d <= ${h2d}`), use('HalfLt', ['de'], cdd, [der, dep])]);
                const cl = X.tc(cdd, [X.inst(X.tc(cdd, [hd], `all x. (x in ${I} -> abs(x - xi) < de -> abs(f[x] - f[xi]) < ${e})`), [x]), xI, X.rw(X.sym(dist), dl, `abs(${x} - xi) < de`, cdd)], `abs(f[${x}] - f[xi]) < ${e}`);
                const fxr = fOf(cdd, x, xI);
                const up = X.tc(cdd, [use('AbsLt', [`f[${x}] - f[xi]`, e], cdd, [...gg, fxr, cl])], `f[${x}] - f[xi] < ${e}`);
                const lt = X.rw(use('SubAdd', ['mu', 'f[xi]'], cdd, gg), use('LtSubAdd', [`f[${x}]`, 'f[xi]', e], cdd, [...gg, fxr, up]), `f[${x}] < mu`, cdd);
                const inS = X.tc(cdd, [dS(x), xI, lt], `${x} in W`);
                const le = X.tc(cdd, [X.inst(ubx, [x]), inS], `${x} <= xi`);
                return X.tc(cdd, [use('LeNotLt', [x, 'xi'], cdd, [le]), use('LtAddPos', ['xi', 'd'], cdd, [...gg, dp])], G);
              }, cd);
            }, c1);
          });
          // 場合2: f(ξ) = μ
          const case2 = X.assume(cx, 'f[xi] = mu', (hc2, c1) => {
            const na = X.raa(c1, 'a != xi', (hn, c2) => {
              const e2 = X.tc(c2, [hn], 'a = xi');
              return [X.rw(hc2, X.rw(e2, h1, 'f[xi] < mu', c2), 'mu < mu', c2), X.inst(X.thm('LtIrrefl'), ['mu'])];
            });
            const nb = X.raa(c1, 'xi != b', (hn, c2) => {
              const e2 = X.tc(c2, [hn], 'xi = b');
              return [X.rw(hc2, X.rw(X.sym(e2), h2, 'mu < f[xi]', c2), 'mu < mu', c2), X.inst(X.thm('LtIrrefl'), ['mu'])];
            });
            return X.exI(X.tc(c1, [xr, axi, na, xib, nb, hc2], 'xi in Real & a < xi & xi < b & f[xi] = mu'), 'xi', 'xi in Real & a < xi & xi < b & f[xi] = mu', 'xi');
          });
          // 場合3: μ < f(ξ)
          const case3 = X.assume(cx, 'mu < f[xi]', (hc3, c1) => {
            const e = 'f[xi] - mu';
            const ep = use('SubPos', ['mu', 'f[xi]'], c1, [...g, hc3]);
            const na = X.raa(c1, 'a != xi', (hn, c2) => {
              const e2 = X.tc(c2, [hn], 'a = xi');
              const l = X.rw(e2, h1, 'f[xi] < mu', c2);
              return [use('LtTrans', ['mu', 'f[xi]', 'mu'], c2, [hc3, l]), X.inst(X.thm('LtIrrefl'), ['mu'])];
            });
            const alx = X.tc(c1, [axi, na], 'a < xi');
            return X.exE(near(c1, e, mem(c1, e, g), ep), 'de', (hd, cd) => {
              const der = X.tc(cd, [hd], 'de in Real'), dep = X.tc(cd, [hd], '0 < de');
              const h2d = 'de * 2^-1';
              return X.exE(use('MinPos', [h2d, 'xi - a'], cd, [...g, der, use('HalfPos', ['de'], cd, [der, dep]), use('SubPos', ['a', 'xi'], cd, [...g, alx])]), 'd', (hdd, cdd) => {
                const dr = X.tc(cdd, [hdd], 'd in Real'), dp = X.tc(cdd, [hdd], '0 < d');
                const gg = [...g, der, dr];
                const w = 'xi - d';
                const dl = use('LeLtTrans', ['d', h2d, 'de'], cdd, [X.tc(cdd, [hdd], `d <= ${h2d}`), use('HalfLt', ['de'], cdd, [der, dep])]);
                const ubw = X.tc(cdd, [ubDef(w, 'W'), mem(cdd, w, gg), X.gen(X.assume(cdd, 's in W', (hs, e1) => {
                  const sI = X.tc(e1, [dS('s'), hs], `s in ${I}`);
                  const sr = X.tc(e1, [cdef('s'), sI], 's in Real');
                  const sle = X.tc(e1, [X.inst(ubx, ['s']), hs], 's <= xi');
                  return X.raa(e1, `s <= ${w}`, (hn, e2) => {
                    const lt = use('NotLeLt', [w, 's'], e2, [...gg, sr, hn]);
                    const ab = use('LeftAbsLe', ['s', 'xi', 'd'], e2, [...gg, sr, sle, lt]);
                    const cl = X.tc(e2, [X.inst(X.tc(e2, [hd], `all x. (x in ${I} -> abs(x - xi) < de -> abs(f[x] - f[xi]) < ${e})`), ['s']), sI, use('LtTrans', ['abs(s - xi)', 'd', 'de'], e2, [ab, dl])], `abs(f[s] - f[xi]) < ${e}`);
                    const fsr = fOf(e2, 's', sI);
                    const lo = X.tc(e2, [use('AbsLt', ['f[s] - f[xi]', e], e2, [...gg, fsr, cl])], `-(${e}) < f[s] - f[xi]`);
                    const ms = use('NegSubLt', ['f[xi]', 'mu', 'f[s]'], e2, [...gg, fsr, lo]);
                    const fs = X.tc(e2, [dS('s'), hs], 'f[s] < mu');
                    return [use('LtTrans', ['mu', 'f[s]', 'mu'], e2, [ms, fs]), X.inst(X.thm('LtIrrefl'), ['mu'])];
                  });
                }), 's')], `UB(${w}, W)`);
                const le = X.tc(cdd, [X.inst(least, [w]), ubw], `xi <= ${w}`);
                return X.tc(cdd, [use('LeNotLt', ['xi', w], cdd, [le]), use('SubLtSelf', ['xi', 'd'], cdd, [...gg, dp])], G);
              }, cd);
            }, c1);
          });
          return X.tc(cx, [use('R13', ['f[xi]', 'mu'], cx, g), case1, case2, case3], G);
        }, cS);
      }, k);
    }))))))), ['f', 'a', 'b', 'mu']));

// ---------------- 最大値・最小値の定理の準備 ----------------
prove('ConstConv', 'all c. (c in Real -> Conv(cseq(c), c))', '[G4]', () => intro(['c'], [], (k) => {
  const cs = use('ConstSeq', ['c'], k);
  return convIntro(k, 'cseq(c)', 'c', X.tc(k, [cs], 'Seq(cseq(c))'), X.hyp(k, 'c in Real'), (c2, he, hp) =>
    tailIntro(c2, 'onew', X.thm('NatOne'), n => `abs(cseq(c)[${n}] - c) < eps`, (cl, hn, hl) => {
      const v = X.tc(cl, [X.inst(X.tc(cl, [cs], 'all n. (n in Nat -> cseq(c)[n] = c)'), ['n']), hn], 'cseq(c)[n] = c');
      const z = calc(cl, 'abs(cseq(c)[n] - c)', [['abs(c - c)', v], ['abs(0)', use('SubSelf', ['c'], cl)], ['0', use('AbsOfNonneg', ['0'], cl, [X.tc(cl, [X.refl('0')], '0 <= 0')])]]);
      return X.rw(X.sym(z), hp, 'abs(cseq(c)[n] - c) < eps', cl);
    }));
}));
const IN = (x) => `all n. (n in Nat -> ${x}[n] in cint(a,b))`;
prove('CintClosed', `all x. all c. all a. all b. (a in Real -> b in Real -> ${IN('x').replace('all n.', '(all n.')}) -> Conv(x,c) -> c in cint(a,b))`, '[G5]', () => X.genAll(
  X.assume([], 'a in Real', (ar, k1) => X.assume(k1, 'b in Real', (br, k2) => X.assume(k2, IN('x'), (hI, k3) => X.assume(k3, 'Conv(x,c)', (hc, k) => {
    const cr = use('ConvR', ['x', 'c'], k, [hc]);
    const ca = use('ConstConv', ['a'], k, [ar]), cb = use('ConstConv', ['b'], k, [br]);
    const csa = use('ConstSeq', ['a'], k, [ar]), csb = use('ConstSeq', ['b'], k, [br]);
    const la = X.gen(X.assume(k, 'n in Nat', (hn, cn) => {
      const v = X.tc(cn, [X.inst(X.tc(cn, [csa], 'all n. (n in Nat -> cseq(a)[n] = a)'), ['n']), hn], 'cseq(a)[n] = a');
      return X.rw(X.sym(v), X.tc(cn, [X.inst(hI, ['n']), hn, X.inst(X.defAx('cint'), ['a', 'b', 'x[n]'])], 'a <= x[n]'), 'cseq(a)[n] <= x[n]', cn);
    }), 'n');
    const lb = X.gen(X.assume(k, 'n in Nat', (hn, cn) => {
      const v = X.tc(cn, [X.inst(X.tc(cn, [csb], 'all n. (n in Nat -> cseq(b)[n] = b)'), ['n']), hn], 'cseq(b)[n] = b');
      return X.rw(X.sym(v), X.tc(cn, [X.inst(hI, ['n']), hn, X.inst(X.defAx('cint'), ['a', 'b', 'x[n]'])], 'x[n] <= b'), 'x[n] <= cseq(b)[n]', cn);
    }), 'n');
    const l1 = use('LimLe', ['cseq(a)', 'x', 'a', 'c'], k, [ca, hc, la]);
    const l2 = use('LimLe', ['x', 'cseq(b)', 'c', 'b'], k, [hc, cb, lb]);
    return X.tc(k, [X.inst(X.defAx('cint'), ['a', 'b', 'c']), cr, l1, l2], 'c in cint(a,b)');
  })))), ['x', 'c', 'a', 'b']));
prove('CintBdd', 'all a. all b. all x. (a in Real -> b in Real -> x in cint(a,b) -> abs(x) <= abs(a) + abs(b))', '[G6]', () => X.genAll(
  X.assume([], 'a in Real', (ar, k1) => X.assume(k1, 'b in Real', (br, k2) => X.assume(k2, 'x in cint(a,b)', (hx, k) => {
    const d = X.inst(X.defAx('cint'), ['a', 'b', 'x']);
    const xr = X.tc(k, [hx, d], 'x in Real'), ax = X.tc(k, [hx, d], 'a <= x'), xb = X.tc(k, [hx, d], 'x <= b');
    const f = [ar, br, xr];
    const S = 'abs(a) + abs(b)';
    const up = use('LeTrans', ['x', 'abs(b)', S], k, [use('LeTrans', ['x', 'b', 'abs(b)'], k, [xb, X.tc(k, [use('AbsBound', ['b'], k, f)], 'b <= abs(b)')]), use('LeAddNonnegL', ['abs(b)', 'abs(a)'], k, [...f, use('AbsNonneg', ['a'], k, f)])]);
    const ma = X.tc(k, [use('AbsBound', ['a'], k, f)], '-abs(a) <= a');
    const s1 = use('NegLe', ['abs(a)', S], k, [...f, use('LeAddNonneg', ['abs(a)', 'abs(b)'], k, [...f, use('AbsNonneg', ['b'], k, f)])]); // -S ≤ -|a|
    const lo = use('LeTrans', [`-(${S})`, '-abs(a)', 'x'], k, [s1, use('LeTrans', ['-abs(a)', 'a', 'x'], k, [ma, ax])]);
    return use('LeAbs', ['x', S], k, [...f, lo, up]);
  }))), ['a', 'b', 'x']));
// 区間内の数列は収束部分列をもつ
prove('BWin', `all x. all a. all b. (a in Real -> b in Real -> Seq(x) -> ${IN('x').replace('all n.', '(all n.')}) -> ex s. ex c. (SubIdx(s) & c in cint(a,b) & Conv(sseq(x,s), c)))`, '[G7]', () => X.genAll(
  X.assume([], 'a in Real', (ar, k1) => X.assume(k1, 'b in Real', (br, k2) => X.assume(k2, 'Seq(x)', (sx, k3) => X.assume(k3, IN('x'), (hI, k) => {
    const B = 'abs(a) + abs(b)';
    const bd = X.tc(k, [X.inst(X.defAx('SeqBdd'), ['x']), sx, X.exI(X.tc(k, [mem(k, B, [ar, br]), X.gen(X.assume(k, 'n in Nat', (hn, cn) => use('CintBdd', ['a', 'b', 'x[n]'], cn, [ar, br, X.tc(cn, [X.inst(hI, ['n']), hn], 'x[n] in cint(a,b)')])), 'n')], `${B} in Real & all n. (n in Nat -> abs(x[n]) <= ${B})`), 'M', 'M in Real & all n. (n in Nat -> abs(x[n]) <= M)', B)], 'SeqBdd(x)');
    return X.exE(use('BW', ['x'], k, [bd]), 'y', (hy, cy) => {
      const sub = X.tc(cy, [hy, X.inst(X.defAx('SubSeq'), ['y', 'x'])], 'Seq(y) & ex s. (SubIdx(s) & all k. (k in Nat -> y[k] = x[s[k]]))');
      return X.exE(X.tc(cy, [hy, X.inst(X.defAx('Cgt'), ['y'])], 'ex al. Conv(y,al)'), 'c', (hc, cc) => X.exE(X.tc(cc, [sub], 'ex s. (SubIdx(s) & all k. (k in Nat -> y[k] = x[s[k]]))'), 's', (hs, cs) => {
        const si = X.tc(cs, [hs], 'SubIdx(s)');
        const ns = X.tc(cs, [si, X.inst(X.defAx('SubIdx'), ['s'])], 'NSeq(s)');
        const ss = use('SubSeqF', ['x', 's'], cs, [sx, ns]);
        const eq = X.gen(X.assume(cs, 'n in Nat', (hn, cn) => X.trans(X.tc(cn, [X.inst(X.tc(cn, [hs], 'all k. (k in Nat -> y[k] = x[s[k]])'), ['n']), hn], 'y[n] = x[s[n]]'),
          X.sym(X.tc(cn, [X.inst(X.tc(cn, [ss], 'all k. (k in Nat -> sseq(x,s)[k] = x[s[k]])'), ['n']), hn], 'sseq(x,s)[n] = x[s[n]]')), cn)), 'n');
        const cv = use('ConvExt', ['y', 'sseq(x,s)', 'c'], cs, [X.tc(cs, [ss], 'Seq(sseq(x,s))'), eq, hc]);
        const inI = X.gen(X.assume(cs, 'n in Nat', (hn, cn) => {
          const v = X.tc(cn, [X.inst(X.tc(cn, [ss], 'all k. (k in Nat -> sseq(x,s)[k] = x[s[k]])'), ['n']), hn], 'sseq(x,s)[n] = x[s[n]]');
          return X.rw(X.sym(v), X.tc(cn, [X.inst(hI, ['s[n]']), use('NSeqVal', ['s', 'n'], cn, [ns, hn])], 'x[s[n]] in cint(a,b)'), 'sseq(x,s)[n] in cint(a,b)', cn);
        }), 'n');
        const cI = use('CintClosed', ['sseq(x,s)', 'c', 'a', 'b'], cs, [ar, br, inI, cv]);
        const G = 'SubIdx(s) & c in cint(a,b) & Conv(sseq(x,s), c)';
        return X.exI(X.exI(X.tc(cs, [si, cI, cv], G), 'c', G, 'c'), 's', `ex c. (${G})`, 's');
      }, cc), cy);
    }, k);
  })))), ['x', 'a', 'b']));
prove('SubLtTwo', 'all x. all y. all e. (x in Real -> y in Real -> e in Real -> x - e < y + e -> x - y < e + e)', '[E44]', () => intro(['x', 'y', 'e'], ['x - e < y + e'], (c, [h]) => {
  const l = use('LtSubAdd', ['x', 'e', 'y + e'], c, [h]);     // x < (y + e) + e
  const l2 = X.rw(use('R2', ['y', 'e', 'e'], c), l, 'x < y + (e + e)', c);
  return use('LtAddSwap', ['y', 'e + e', 'x'], c, [l2]);
}));

prove('SubLtAnti', 'all z. all x. all y. (z in Real -> x in Real -> y in Real -> x < y -> z - y < z - x)', '[E45]', () => intro(['z', 'x', 'y'], ['x < y'], (c, [h]) => {
  const l = use('R14', ['-y', '-x', 'z'], c, [use('NegLt', ['x', 'y'], c, [h])]);
  const e = t => X.trans(use('R3', [`-${t}`, 'z'], c), X.sym(X.inst(X.defAx('minus'), ['z', t])), c);
  return X.rw(e('x'), X.rw(e('y'), l, 'z - y < -x + z', c), 'z - y < z - x', c);
}));

// ---------------- 定理 2.17: 最大値・最小値の定理 ----------------

const PSIB = 'x in cint(a,b) & iota(k) < f[x]';
const ccB = ccInst(PSIB);
const PSIM = 'x in cint(a,b) & si - iota(k)^-1 < f[x]';
const ccM = ccInst(PSIM);
// q: 区間内の数列, s: 添字列. f∘(q∘s) が f(c) に収束し, その値は f(q_{s_n})
function subImage(cc, rf, Isub, allC, sq, hq, si, cI, conv) {
  const ns = X.tc(cc, [si, X.inst(X.defAx('SubIdx'), ['s'])], 'NSeq(s)');
  const ss = use('SubSeqF', ['q', 's'], cc, [sq, ns]);
  const val = (cn, n, hn) => X.tc(cn, [X.inst(X.tc(cn, [ss], 'all k. (k in Nat -> sseq(q,s)[k] = q[s[k]])'), [n]), hn], `sseq(q,s)[${n}] = q[s[${n}]]`);
  const inI = X.gen(X.assume(cc, 'n in Nat', (hn, cn) => X.rw(X.sym(val(cn, 'n', hn)), X.tc(cn, [X.inst(hq, ['s[n]']), use('NSeqVal', ['s', 'n'], cn, [ns, hn])], `q[s[n]] in ${I}`), `sseq(q,s)[n] in ${I}`, cn)), 'n');
  const ci = X.tc(cc, [X.inst(allC, ['c']), cI], `ContIn(f, ${I}, c)`);
  const fc = use('ContInSeq', ['f', I, 'c', 'sseq(q,s)'], cc, [ci, X.tc(cc, [ss], 'Seq(sseq(q,s))'), inI, conv]);
  const dom1 = X.gen(X.assume(cc, 'n in Nat', (hn, cn) => subE(cn, Isub, I, 'dom(f)', 'sseq(q,s)[n]', X.tc(cn, [X.inst(inI, ['n']), hn], `sseq(q,s)[n] in ${I}`))), 'n');
  const cs = use('CompSeq', ['f', 'sseq(q,s)'], cc, [rf, X.tc(cc, [ss], 'Seq(sseq(q,s))'), dom1]);
  const fval = (cn, n, hn) => X.trans(X.tc(cn, [X.inst(X.tc(cn, [cs], 'all n. (n in Nat -> compseq(f,sseq(q,s))[n] = f[sseq(q,s)[n]])'), [n]), hn], `compseq(f,sseq(q,s))[${n}] = f[sseq(q,s)[${n}]]`),
    K.cong(val(cn, n, hn), `f[sseq(q,s)[${n}]]`, cn), cn);  // = f[q[s[n]]]
  return { fc, fval, ns };
}
prove('EVTBdd', `all f. all a. all b. (ContOn(f, ${I}) -> a in Real -> b in Real -> ex M. (M in Real & all x. (x in ${I} -> f[x] <= M)))`, '[G8]', () => X.genAll(
  X.assume([], `ContOn(f, ${I})`, (hco, k1) => X.assume(k1, 'a in Real', (ar, k2) => X.assume(k2, 'b in Real', (br, k) => {
    const G = `ex M. (M in Real & all x. (x in ${I} -> f[x] <= M))`;
    const rf = X.tc(k, [hco, coDef('f', I)], 'RFn(f)'), Isub = X.tc(k, [hco, coDef('f', I)], `${I} sub dom(f)`);
    const allC = X.tc(k, [hco, coDef('f', I)], `all c. (c in ${I} -> ContIn(f, ${I}, c))`);
    const fOf = (cc, x, hxI) => mem(cc, `f[${x}]`, [rf, subE(cc, Isub, I, 'dom(f)', x, hxI)]);
    return X.raa(k, G, (hn, c0) => {
      const pre = X.gen(X.assume(c0, 'k in Nat', (hk, ck) => {
        const ik = mem(ck, 'iota(k)', [hk]);
        const notM = X.tc(ck, [hn], `all M. ~(M in Real & all x. (x in ${I} -> f[x] <= M))`);
        const nall = X.tc(ck, [X.inst(notM, ["iota(k)"]), ik], `~ all x. (x in ${I} -> f[x] <= iota(k))`);
        return X.exE(X.notAllToEx(nall), 'x', (hx, cx) => {
          const xI = X.tc(cx, [hx], `x in ${I}`);
          const xr = X.tc(cx, [xI, X.inst(X.defAx('cint'), ['a', 'b', 'x'])], 'x in Real');
          const lt = use('NotLeLt', ['iota(k)', 'f[x]'], cx, [ik, fOf(cx, 'x', xI), X.tc(cx, [hx], '~ f[x] <= iota(k)')]);
          return X.exI(X.tc(cx, [xr, xI, lt], `x in Real & (${PSIB})`), 'x', `x in Real & (${PSIB})`, 'x');
        }, ck);
      }), 'k');
      return [X.exE(ccB(c0, [pre]), 'q', (hq0, cq) => {
        const sq = X.tc(cq, [hq0], 'Seq(q)');
        const pq = X.tc(cq, [hq0], `all k. (k in Nat -> ${PSIB.replace(/\bx\b/g, 'q[k]')})`);
        const hq = X.gen(X.assume(cq, 'n in Nat', (hn, cn) => X.tc(cn, [X.inst(pq, ['n']), hn], `q[n] in ${I}`)), 'n');
        return X.exE(use('BWin', ['q', 'a', 'b'], cq, [ar, br, sq, hq]), 's', (hs0, cs0) => X.exE(hs0, 'c', (hs, cs) => {
          const si = X.tc(cs, [hs], 'SubIdx(s)'), cI = X.tc(cs, [hs], `c in ${I}`), conv = X.tc(cs, [hs], 'Conv(sseq(q,s), c)');
          const { fc, fval, ns } = subImage(cs, rf, Isub, allC, sq, hq, si, cI, conv);
          const bd = X.tc(cs, [use('ConvBdd', ['compseq(f,sseq(q,s))', 'f[c]'], cs, [fc]), X.inst(X.defAx('SeqBdd'), ['compseq(f,sseq(q,s))'])], 'ex M. (M in Real & all n. (n in Nat -> abs(compseq(f,sseq(q,s))[n]) <= M))');
          return X.exE(bd, 'M', (hM, cM) => {
            const mr = X.tc(cM, [hM], 'M in Real');
            const B = 'abs(M) + 1';
            const bp = use('LeLtTrans', ['0', 'abs(M)', B], cM, [use('AbsNonneg', ['M'], cM, [mr]), use('LtAddOne', ['abs(M)'], cM, [mr])]);
            return X.exE(use('Archimedes', ['1', B], cM, [X.thm('R1_1'), mem(cM, B, [mr]), X.tc(cM, [X.thm('ZeroLtOne')], '0 < 1'), bp]), 'K', (hK, cK) => {
              const kn = X.tc(cK, [hK], 'K in Nat');
              const g = [mr, kn];
              const kb = X.rw(use('R8', ['iota(K)'], cK, g), X.tc(cK, [hK], `${B} < iota(K) * 1`), `${B} < iota(K)`, cK);
              const sK = use('NSeqVal', ['s', 'K'], cK, [ns, kn]);
              const ps = X.tc(cK, [X.inst(pq, ['s[K]']), sK], `q[s[K]] in ${I} & iota(s[K]) < f[q[s[K]]]`);
              const ge = X.tc(cK, [X.inst(use('IdxGe', ['s'], cK, [si]), ['K']), kn], 'K <= s[K]');
              const im = use('IotaMono', ['K', 's[K]'], cK, [kn, sK, ge]);
              const bnd = X.tc(cK, [X.inst(X.tc(cK, [hM], 'all n. (n in Nat -> abs(compseq(f,sseq(q,s))[n]) <= M)'), ['K']), kn], 'abs(compseq(f,sseq(q,s))[K]) <= M');
              const bnd2 = X.rw(fval(cK, 'K', kn), bnd, 'abs(f[q[s[K]]]) <= M', cK);
              const fq = fOf(cK, 'q[s[K]]', X.tc(cK, [ps], `q[s[K]] in ${I}`));
              const le1 = use('LeTrans', ['f[q[s[K]]]', 'abs(f[q[s[K]]])', 'M'], cK, [X.tc(cK, [use('AbsBound', ['f[q[s[K]]]'], cK, [fq])], 'f[q[s[K]]] <= abs(f[q[s[K]]])'), bnd2]);
              const le2 = use('LeTrans', ['f[q[s[K]]]', 'M', 'abs(M)'], cK, [le1, X.tc(cK, [use('AbsBound', ['M'], cK, [mr])], 'M <= abs(M)')]);
              const lt = use('LeLtTrans', ['f[q[s[K]]]', 'abs(M)', 'iota(K)'], cK, [le2, use('LtTrans', ['abs(M)', B, 'iota(K)'], cK, [use('LtAddOne', ['abs(M)'], cK, [mr]), kb])]);
              const lt2 = use('LtLeTrans', ['f[q[s[K]]]', 'iota(K)', 'iota(s[K])'], cK, [lt, im]);
              return X.tc(cK, [use('LtTrans', ['f[q[s[K]]]', 'iota(s[K])', 'f[q[s[K]]]'], cK, [lt2, X.tc(cK, [ps], 'iota(s[K]) < f[q[s[K]]]')]), X.inst(X.thm('LtIrrefl'), ['f[q[s[K]]]'])], '0 < 0');
            }, cM);
          }, cs);
        }, cs0), cq);
      }, c0), X.inst(X.thm('LtIrrefl'), ['0'])];
    });
  }))), ['f', 'a', 'b']));

prove('EVT', `all f. all a. all b. (ContOn(f, ${I}) -> a in Real -> b in Real -> a <= b -> ex xi. (xi in ${I} & all x. (x in ${I} -> f[x] <= f[xi])))`, '定理2.17', () => X.genAll(
  X.assume([], `ContOn(f, ${I})`, (hco, k1) => X.assume(k1, 'a in Real', (ar, k2) => X.assume(k2, 'b in Real', (br, k3) => X.assume(k3, 'a <= b', (hab, k) => {
    const rf = X.tc(k, [hco, coDef('f', I)], 'RFn(f)'), Isub = X.tc(k, [hco, coDef('f', I)], `${I} sub dom(f)`);
    const allC = X.tc(k, [hco, coDef('f', I)], `all c. (c in ${I} -> ContIn(f, ${I}, c))`);
    const fOf = (cc, x, hxI) => mem(cc, `f[${x}]`, [rf, subE(cc, Isub, I, 'dom(f)', x, hxI)]);
    const aI = X.tc(k, [X.inst(X.defAx('cint'), ['a', 'b', 'a']), ar, X.tc(k, [X.refl('a')], 'a <= a'), hab], `a in ${I}`);
    const sep = X.inst(X.axiom('Sep', 'all f. all A. all B. ex T. all y. (y in T <-> y in B & ex x. (x in A & y = f[x]))'), ['f', I, 'Real']);
    return X.exE(sep, 'T', (hT, cT) => {
      const dT = t => X.inst(hT, [t]);
      const inT = (cc, x, hxI) => X.tc(cc, [dT(`f[${x}]`), fOf(cc, x, hxI), X.exI(X.tc(cc, [hxI, X.refl(`f[${x}]`)], `${x} in ${I} & f[${x}] = f[${x}]`), 'z9', `z9 in ${I} & f[${x}] = f[z9]`, x)], `f[${x}] in T`);
      const Tr = X.tc(cT, [X.inst(X.defAx('sub'), ['T', 'Real']), X.gen(X.assume(cT, 'u in T', (hu, cu) => X.tc(cu, [dT('u'), hu], 'u in Real')), 'u')], 'T sub Real');
      return X.exE(use('EVTBdd', ['f', 'a', 'b'], cT, [hco, ar, br]), 'M', (hM, cM) => {
        const ub = X.tc(cM, [X.inst(X.defAx('UB'), ['M', 'T']), X.tc(cM, [hM], 'M in Real'), X.gen(X.assume(cM, 'y in T', (hy, cy) =>
          X.exE(X.tc(cy, [dT('y'), hy], `ex x. (x in ${I} & y = f[x])`), 'x', (hx, cx) => X.rw(X.sym(X.tc(cx, [hx], 'y = f[x]')), X.tc(cx, [X.inst(X.tc(cx, [hM], `all x. (x in ${I} -> f[x] <= M)`), ['x']), hx], 'f[x] <= M'), 'y <= M', cx), cy)), 'y')], 'UB(M, T)');
        return X.exE(use('R16', ['T'], cM, [Tr, use('ExNonempty', ['T', 'f[a]'], cM, [inT(cM, 'a', aI)]), X.exI(ub, 'b', 'UB(b, T)', 'M')]), 'si', (hsi, csi) => {
          const sr = X.tc(csi, [hsi, X.inst(X.defAx('IsSup'), ['si', 'T']), X.inst(X.defAx('UB'), ['si', 'T'])], 'si in Real');
          const ubs = X.tc(csi, [hsi, X.inst(X.defAx('IsSup'), ['si', 'T']), X.inst(X.defAx('UB'), ['si', 'T'])], 'all x. (x in T -> x <= si)');
          const pre = X.gen(X.assume(csi, 'k in Nat', (hk, ck) => {
            const ip = use('IotaPos', ['k'], ck, [hk]);
            const kz = X.neSym(use('LtNe', ['0', 'iota(k)'], ck, [ip]));
            return X.exE(use('SupApprox', ['si', 'T', 'iota(k)^-1'], ck, [Tr, hsi, mem(ck, 'iota(k)^-1', [hk, kz]), use('InvPos', ['iota(k)'], ck, [hk, ip])]), 'y', (hy, cy) =>
              X.exE(X.tc(cy, [dT('y'), hy], `ex x. (x in ${I} & y = f[x])`), 'x', (hx, cx) => {
                const xI = X.tc(cx, [hx], `x in ${I}`);
                const lt = X.rw(X.tc(cx, [hx], 'y = f[x]'), X.tc(cx, [hy], 'si - iota(k)^-1 < y'), 'si - iota(k)^-1 < f[x]', cx);
                return X.exI(X.tc(cx, [X.tc(cx, [xI, X.inst(X.defAx('cint'), ['a', 'b', 'x'])], 'x in Real'), xI, lt], `x in Real & (${PSIM})`), 'x', `x in Real & (${PSIM})`, 'x');
              }, cy), ck);
          }), 'k');
          return X.exE(ccM(csi, [pre]), 'q', (hq0, cq) => {
            const sq = X.tc(cq, [hq0], 'Seq(q)');
            const pq = X.tc(cq, [hq0], `all k. (k in Nat -> ${PSIM.replace(/\bx\b/g, 'q[k]')})`);
            const hq = X.gen(X.assume(cq, 'n in Nat', (hn, cn) => X.tc(cn, [X.inst(pq, ['n']), hn], `q[n] in ${I}`)), 'n');
            return X.exE(use('BWin', ['q', 'a', 'b'], cq, [ar, br, sq, hq]), 's', (hs0, cs0) => X.exE(hs0, 'c', (hs, cs) => {
              const si = X.tc(cs, [hs], 'SubIdx(s)'), cI = X.tc(cs, [hs], `c in ${I}`), conv = X.tc(cs, [hs], 'Conv(sseq(q,s), c)');
              const { fc, fval, ns } = subImage(cs, rf, Isub, allC, sq, hq, si, cI, conv);
              const fcr = fOf(cs, 'c', cI);
              const fcs = X.tc(cs, [X.inst(ubs, ['f[c]']), inT(cs, 'c', cI)], 'f[c] <= si');
              const sfc = X.raa(cs, 'si <= f[c]', (hn, c2) => {
                const lt = use('NotLeLt', ['f[c]', 'si'], c2, [fcr, sr, hn]);
                const d = 'si - f[c]', e = '(si - f[c]) * 2^-1';
                const g = [sr, fcr];
                const dp = use('SubPos', ['f[c]', 'si'], c2, [...g, lt]);
                const er = mem(c2, e, g), ep = use('HalfPos', [d], c2, [...g, dp]);
                return [X.exE(use('ConvE', ['compseq(f,sseq(q,s))', 'f[c]', e], c2, [fc, er, ep]), 'N1', (h1, d1) => X.exE(use('ArchInv', [e], d1, [er, ep]), 'K', (hK, d2) => {
                  const n1 = X.tc(d2, [h1], 'N1 in Nat'), kn = X.tc(d2, [hK], 'K in Nat');
                  const Mx = 'cup(N1, K)';
                  const mn = use('NatCup', ['N1', 'K'], d2, [n1, kn]);
                  const sM = use('NSeqVal', ['s', Mx], d2, [ns, mn]);
                  const near = X.rw(fval(d2, Mx, mn), tailAt(d2, h1, 'N1', n => `abs(compseq(f,sseq(q,s))[${n}] - f[c]) < ${e}`, Mx, mn, X.inst(X.thm('LeCupL'), ['N1', 'K'])), `abs(f[q[s[${Mx}]]] - f[c]) < ${e}`, d2);
                  const ps = X.tc(d2, [X.inst(pq, [`s[${Mx}]`]), sM], `q[s[${Mx}]] in ${I} & si - iota(s[${Mx}])^-1 < f[q[s[${Mx}]]]`);
                  const fq = fOf(d2, `q[s[${Mx}]]`, X.tc(d2, [ps], `q[s[${Mx}]] in ${I}`));
                  const gg = [...g, fq, er, mn, kn, sM];
                  const up = X.rw(use('SubAdd', [`f[q[s[${Mx}]]]`, 'f[c]'], d2, gg), use('R14', [`f[q[s[${Mx}]]] - f[c]`, e, 'f[c]'], d2, [...gg, X.tc(d2, [use('AbsLt', [`f[q[s[${Mx}]]] - f[c]`, e], d2, [...gg, near])], `f[q[s[${Mx}]]] - f[c] < ${e}`)]), `f[q[s[${Mx}]]] < ${e} + f[c]`, d2);
                  const up2 = X.rw(use('R3', [e, 'f[c]'], d2, gg), up, `f[q[s[${Mx}]]] < f[c] + ${e}`, d2);
                  // ι(s_M)^{-1} ≤ ι(M)^{-1} ≤ ι(K)^{-1} < e
                  const geM = X.tc(d2, [X.inst(use('IdxGe', ['s'], d2, [si]), [Mx]), mn], `${Mx} <= s[${Mx}]`);
                  const i1 = use('IotaInvMono', [Mx, `s[${Mx}]`], d2, [mn, sM, geM]);
                  const i2 = use('IotaInvMono', ['K', Mx], d2, [kn, mn, X.inst(X.thm('LeCupR'), ['N1', 'K'])]);
                  const ie = use('LeLtTrans', [`iota(s[${Mx}])^-1`, 'iota(K)^-1', e], d2, [use('LeTrans', [`iota(s[${Mx}])^-1`, `iota(${Mx})^-1`, 'iota(K)^-1'], d2, [i1, i2]), X.tc(d2, [hK], `iota(K)^-1 < ${e}`)]);
                  const sz = X.neSym(use('LtNe', ['0', `iota(s[${Mx}])`], d2, [use('IotaPos', [`s[${Mx}]`], d2, [sM])]));
                  const lo = use('LtTrans', [`si - ${e}`, `si - iota(s[${Mx}])^-1`, `f[q[s[${Mx}]]]`], d2, [use('SubLtAnti', ['si', `iota(s[${Mx}])^-1`, e], d2, [...gg, sz, ie]), X.tc(d2, [ps], `si - iota(s[${Mx}])^-1 < f[q[s[${Mx}]]]`)]);
                  const both = use('LtTrans', [`si - ${e}`, `f[q[s[${Mx}]]]`, `f[c] + ${e}`], d2, [lo, up2]);
                  const r = X.rw(use('HalfSum', [d], d2, gg), use('SubLtTwo', ['si', 'f[c]', e], d2, [...gg, both]), `${d} < ${d}`, d2);
                  return X.tc(d2, [r, X.inst(X.thm('LtIrrefl'), [d])], '0 < 0');
                }, d1), c2), X.inst(X.thm('LtIrrefl'), ['0'])];
              });
              const eqc = use('LeAntisym', ['f[c]', 'si'], cs, [fcs, sfc]);
              const all = X.gen(X.assume(cs, `x in ${I}`, (hx, cx) => X.rw(X.sym(eqc), X.tc(cx, [X.inst(ubs, ['f[x]']), inT(cx, 'x', hx)], 'f[x] <= si'), 'f[x] <= f[c]', cx)), 'x');
              const G = c => `${c} in ${I} & all x. (x in ${I} -> f[x] <= f[${c}])`;
              return X.exI(X.tc(cs, [cI, all], G('c')), 'xi', G('xi'), 'c');
            }, cs0), cq);
          }, csi);
        }, cM);
      }, cT);
    }, k);
  })))), ['f', 'a', 'b']));

// 最小値: -f に最大値の定理を適用する
prove('EVTMin', `all f. all a. all b. (ContOn(f, ${I}) -> a in Real -> b in Real -> a <= b -> ex xi. (xi in ${I} & all x. (x in ${I} -> f[xi] <= f[x])))`, '定理2.17(最小値)', () => X.genAll(
  X.assume([], `ContOn(f, ${I})`, (hco, k1) => X.assume(k1, 'a in Real', (ar, k2) => X.assume(k2, 'b in Real', (br, k3) => X.assume(k3, 'a <= b', (hab, k) => {
    const F = 'fscal(-1,f)';
    const m1 = mem(k, '-1', []);
    const rf = X.tc(k, [hco, coDef('f', I)], 'RFn(f)'), Isub = X.tc(k, [hco, coDef('f', I)], `${I} sub dom(f)`);
    const FS = use('FScal', ['-1', 'f'], k, [m1, rf]);
    const domIff = X.tc(k, [FS], `all x. (x in dom(${F}) <-> x in dom(f))`);
    const valF = X.tc(k, [FS], `all x. (x in dom(${F}) -> ${F}[x] = -1 * f[x])`);
    const allC = X.gen(X.assume(k, `c in ${I}`, (hc, cc) => use('ContInScal', ['-1', 'f', I, 'c'], cc, [m1, X.tc(cc, [X.inst(X.tc(cc, [hco, coDef('f', I)], `all c. (c in ${I} -> ContIn(f, ${I}, c))`), ['c']), hc], `ContIn(f, ${I}, c)`)])), 'c');
    const sub = X.tc(k, [X.inst(X.defAx('sub'), [I, `dom(${F})`]), X.gen(X.assume(k, `u in ${I}`, (hu, cu) => X.tc(cu, [subE(cu, Isub, I, 'dom(f)', 'u', hu), X.inst(domIff, ['u'])], `u in dom(${F})`)), 'u')], `${I} sub dom(${F})`);
    const co = X.tc(k, [coDef(F, I), X.tc(k, [FS], `RFn(${F})`), sub, allC], `ContOn(${F}, ${I})`);
    return X.exE(use('EVT', [F, 'a', 'b'], k, [co, ar, br, hab]), 'xi', (hx, cx) => {
      const xI = X.tc(cx, [hx], `xi in ${I}`);
      const val = (cc, x, hxI) => {
        const xd = subE(cc, Isub, I, 'dom(f)', x, hxI);
        const fx = mem(cc, `f[${x}]`, [rf, xd]);
        const v = X.tc(cc, [X.inst(valF, [x]), X.inst(domIff, [x]), xd], `${F}[${x}] = -1 * f[${x}]`);
        const one = calc(cc, `1 * f[${x}]`, [[`f[${x}] * 1`, use('R7', ['1', `f[${x}]`], cc, [fx])], [`f[${x}]`, use('R8', [`f[${x}]`], cc, [fx])]]);
        return calc(cc, `${F}[${x}]`, [[`-1 * f[${x}]`, v], [`-(1 * f[${x}])`, use('NegMul', ['1', `f[${x}]`], cc, [fx])], [`-f[${x}]`, one]]);  // = -f(x)
      };
      const all = X.gen(X.assume(cx, `x in ${I}`, (hxx, c2) => {
        const l = X.tc(c2, [X.inst(X.tc(c2, [hx], `all x. (x in ${I} -> ${F}[x] <= ${F}[xi])`), ['x']), hxx], `${F}[x] <= ${F}[xi]`);
        const l2 = X.rw(val(c2, 'xi', xI), X.rw(val(c2, 'x', hxx), l, `-f[x] <= ${F}[xi]`, c2), '-f[x] <= -f[xi]', c2);
        const fx = mem(c2, 'f[x]', [rf, subE(c2, Isub, I, 'dom(f)', 'x', hxx)]), fxi = mem(c2, 'f[xi]', [rf, subE(c2, Isub, I, 'dom(f)', 'xi', xI)]);
        const l3 = use('NegLe', ['-f[x]', '-f[xi]'], c2, [mem(c2, '-f[x]', [fx]), mem(c2, '-f[xi]', [fxi]), l2]);
        return X.rw(use('NegNeg', ['f[x]'], c2, [fx]), X.rw(use('NegNeg', ['f[xi]'], c2, [fxi]), l3, 'f[xi] <= -(-f[x])', c2), 'f[xi] <= f[x]', c2);
      }), 'x');
      const G = `xi in ${I} & all x. (x in ${I} -> f[xi] <= f[x])`;
      return X.exI(X.tc(cx, [xI, all], G), 'xi', G, 'xi');
    }, k);
  })))), ['f', 'a', 'b']));

module.exports = { subImage };

