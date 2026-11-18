'use strict';
// テキスト第4章 2節 2.4: 逆関数 (定義2.20, 定理2.21)
const K = require('./kit');
const { X, C, prove, use, calc, mem, P, T } = K;
const { def, fthm } = require('./theory');
const L = require('./lang');
require('./p_uc');

// ---------------- 記号・定義 ----------------
L.defFunc('finv', 1, a => `${a[0]}^{-1}`, 90);
L.defPred('StrInc', 2, a => `\\mathrm{StrInc}(${a.join(',')})`);
L.defPred('Itv', 1, a => `\\mathrm{Itv}(${a[0]})`);
L.defPred('Inj', 1, a => `\\mathrm{Inj}(${a[0]})`);
def('StrInc', 'all f. all A. (StrInc(f,A) <-> all x. all y. (x in A -> y in A -> x < y -> f[x] < f[y]))', 'DefStrInc');
def('Itv', 'all I. (Itv(I) <-> I sub Real & all x. all y. all z. (x in I -> z in I -> y in Real -> x <= y -> y <= z -> y in I))', 'DefItv');
def('Inj', 'all f. (Inj(f) <-> all x. all y. (x in dom(f) -> y in dom(f) -> f[x] = f[y] -> x = y))', 'DefInj');
fthm('InvFn', 'all f. (RFn(f) -> Inj(f) -> RFn(finv(f)) & (all y. (y in dom(finv(f)) <-> ex x. (x in dom(f) & y = f[x]))) & (all x. (x in dom(f) -> finv(f)[f[x]] = x)) & all y. (y in dom(finv(f)) -> finv(f)[y] in dom(f) & f[finv(f)[y]] = y))', '[S26]', '逆関数');

// ---------------- 補助手続き ----------------
const G = 'finv(f)';
// c ⊢ StrInc(F, A), x, y ∈ A, x < y  →  c ⊢ F[x] < F[y]
function inc(c, hS, F, A, x, y, hx, hy, hlt) {
  const all = X.tc(c, [hS, X.inst(X.defAx('StrInc'), [T(F), T(A)])], `all x. all y. (x in ${A} -> y in ${A} -> x < y -> ${F}[x] < ${F}[y])`);
  return X.tc(c, [X.inst(all, [T(x), T(y)]), hx, hy, hlt], `${F}[${x}] < ${F}[${y}]`);
}
// c ⊢ Itv(I), x, z ∈ I, t ∈ ℝ, x ≤ t ≤ z  →  c ⊢ t ∈ I
function itv(c, hI, I, x, t, z, hx, hz, ht, h1, h2) {
  const all = X.tc(c, [hI, X.inst(X.defAx('Itv'), [T(I)])], `all x. all y. all z. (x in ${I} -> z in ${I} -> y in Real -> x <= y -> y <= z -> y in ${I})`);
  return X.tc(c, [X.inst(all, [T(x), T(t), T(z)]), hx, hz, ht, h1, h2], `${t} in ${I}`);
}
// 逆関数の基本性質 (inv: c ⊢ InvFn の結論)
const invAll = (c, inv) => X.tc(c, [inv], `all y. (y in dom(${G}) -> ${G}[y] in dom(f) & f[${G}[y]] = y)`);
function invAt(c, inv, y, hy) { // c ⊢ g[y] ∈ dom f ∧ f[g[y]] = y
  const l = X.tc(c, [X.inst(invAll(c, inv), [T(y)]), hy], `${G}[${y}] in dom(f) & f[${G}[${y}]] = ${y}`);
  return [X.tc(c, [l], `${G}[${y}] in dom(f)`), X.tc(c, [l], `f[${G}[${y}]] = ${y}`)];
}
const invFx = (c, inv, x, hx) => X.tc(c, [X.inst(X.tc(c, [inv], `all x. (x in dom(f) -> ${G}[f[x]] = x)`), [T(x)]), hx], `${G}[f[${x}]] = ${x}`);
function inDomG(c, inv, x, hx) { // x ∈ dom f → f[x] ∈ dom g
  const iff = X.inst(X.tc(c, [inv], `all y. (y in dom(${G}) <-> ex x. (x in dom(f) & y = f[x]))`), [T(`f[${x}]`)]);
  const ex = X.exI(X.tc(c, [hx, X.refl(`f[${x}]`)], `${x} in dom(f) & f[${x}] = f[${x}]`), 'x', `x in dom(f) & f[${x}] = f[x]`, x);
  return X.tc(c, [iff, ex], `f[${x}] in dom(${G})`);
}
const domR = (c, hR, F, x, hx) => use('RFnDom', [F, x], c, [hR, hx]);

// ---------------- 体の補題 ----------------
prove('SubLeAnti', 'all z. all x. all y. (z in Real -> x in Real -> y in Real -> x <= y -> z - y <= z - x)', '[E51]', () => K.intro(['z', 'x', 'y'], ['x <= y'], (c, [h]) => {
  const l = use('LeAddRight', ['-y', '-x', 'z'], c, [use('NegLe', ['x', 'y'], c, [h])]);
  const e1 = calc(c, '-y + z', [['z + -y', use('R3', ['-y', 'z'], c)], ['z - y', X.sym(X.inst(X.defAx('minus'), [T('z'), T('y')]))]]);
  const e2 = calc(c, '-x + z', [['z + -x', use('R3', ['-x', 'z'], c)], ['z - x', X.sym(X.inst(X.defAx('minus'), [T('z'), T('x')]))]]);
  return X.rw(e2, X.rw(e1, l, 'z - y <= -x + z', c), 'z - y <= z - x', c);
}));

// ---------------- 狭義単調増加なら単射 ----------------
prove('StrIncInj', 'all f. (RFn(f) -> StrInc(f, dom(f)) -> Inj(f))', '[I1]', () => X.gen(X.assume([], 'RFn(f)', (hR, c1) => X.assume(c1, 'StrInc(f, dom(f))', (hS, c) => {
  const body = X.assume(c, 'x in dom(f)', (hx, c2) => X.assume(c2, 'y in dom(f)', (hy, c3) => X.assume(c3, 'f[x] = f[y]', (he, c4) => {
    const tri = use('R13', ['x', 'y'], c4, [domR(c4, hR, 'f', 'x', hx), domR(c4, hR, 'f', 'y', hy)]);
    return K.cases(c4, tri, [
      (h, c5) => X.tc(c5, [X.rw(he, inc(c5, hS, 'f', 'dom(f)', 'x', 'y', hx, hy, h), 'f[y] < f[y]', c5), X.inst(X.thm('LtIrrefl'), [T('f[y]')])], 'x = y'),
      (h, c5) => h,
      (h, c5) => X.tc(c5, [X.rw(he, inc(c5, hS, 'f', 'dom(f)', 'y', 'x', hy, hx, h), 'f[y] < f[y]', c5), X.inst(X.thm('LtIrrefl'), [T('f[y]')])], 'x = y')], 'x = y');
  })));
  return X.tc(c, [X.inst(X.defAx('Inj'), [T('f')]), X.genAll(body, ['x', 'y'])], 'Inj(f)');
})), 'f'));

// 文脈 [RFn f, StrInc(f, dom f)] での共通の準備
function setup(c, hR, hS) {
  const inj = use('StrIncInj', ['f'], c, [hR, hS]);
  const inv = use('InvFn', ['f'], c, [hR, inj]);
  return { inv, gR: X.tc(c, [inv], `RFn(${G})`) };
}

// ---------------- 逆関数も狭義単調増加 ----------------
prove('InvMono', `all f. (RFn(f) -> StrInc(f, dom(f)) -> StrInc(${G}, dom(${G})))`, '[I2]', () => X.gen(X.assume([], 'RFn(f)', (hR, c1) => X.assume(c1, 'StrInc(f, dom(f))', (hS, c) => {
  const { inv } = setup(c, hR, hS);
  const body = X.assume(c, `x in dom(${G})`, (hx, c2) => X.assume(c2, `y in dom(${G})`, (hy, c3) => X.assume(c3, 'x < y', (hlt, c4) => {
    const a = `${G}[x]`, b = `${G}[y]`;
    const [ad, fa] = invAt(c4, inv, 'x', hx), [bd, fb] = invAt(c4, inv, 'y', hy);
    const ar = domR(c4, hR, 'f', a, ad), br = domR(c4, hR, 'f', b, bd);
    const irr = X.inst(X.thm('LtIrrefl'), [T('x')]);
    const notLe = X.assume(c4, `${b} <= ${a}`, (hle, c5) => {
      const d = X.tc(c5, [hle], `${b} < ${a} | ${b} = ${a}`);
      const xx = K.cases(c5, d, [
        (h, c6) => use('LtTrans', ['x', 'y', 'x'], c6, [hlt, X.rw(fa, X.rw(fb, inc(c6, hS, 'f', 'dom(f)', b, a, bd, ad, h), `y < f[${a}]`, c6), 'y < x', c6)]),
        (h, c6) => {
          const l1 = X.rw(X.sym(fb), hlt, `x < f[${b}]`, c6);
          return X.rw(fa, X.rw(h, l1, `x < f[${a}]`, c6), 'x < x', c6);
        }], 'x < x');
      return X.tc(c5, [xx, irr], `~ ${b} <= ${a}`);
    });
    return use('NotLeLt', [a, b], c4, [ar, br, X.tc(c4, [notLe], `~ ${b} <= ${a}`)]);
  })));
  return X.tc(c, [X.inst(X.defAx('StrInc'), [T(G), T(`dom(${G})`)]), X.genAll(body, ['x', 'y'])], `StrInc(${G}, dom(${G}))`);
})), 'f'));

// ---------------- 定理2.21 の証明の準備: 右側・左側の評価 ----------------
const H3 = ['RFn(f)', 'Itv(dom(f))', 'StrInc(f, dom(f))'];
function hyps(hs, body) { // hs を順に仮定して body(ctx, lines)
  const rec = (i, ctx, ls) => i < hs.length ? X.assume(ctx, hs[i], (h, c) => rec(i + 1, c, [...ls, h])) : body(ctx, ls);
  return rec(0, [], []);
}
const up = `ex de. (de in Real & 0 < de & all y. (y in dom(${G}) -> y < y0 + de -> ${G}[y] < ${G}[y0] + eps))`;
const down = `ex de. (de in Real & 0 < de & all y. (y in dom(${G}) -> y0 - de < y -> ${G}[y0] - eps < ${G}[y]))`;
function sideProof(dir) {
  return () => X.genAll(hyps([...H3, `y0 in dom(${G})`, 'eps in Real', '0 < eps'], (c, [hR, hI, hS, hy0, he, hp]) => {
    const { inv } = setup(c, hR, hS);
    const x0 = `${G}[y0]`;
    const [x0d, fx0] = invAt(c, inv, 'y0', hy0);
    const x0r = domR(c, hR, 'f', x0, x0d);
    const y0r = X.rw(fx0, use('RFnVal', ['f', x0], c, [hR, x0d]), 'y0 in Real', c);
    const gS = use('InvMono', ['f'], c, [hR, hS]);
    const E = dir === 'up' ? `ex u. (u in dom(f) & ${x0} < u)` : `ex u. (u in dom(f) & u < ${x0})`;
    const goal = dir === 'up' ? up : down;
    const R = dir === "up" ? (y, de) => `${y} < y0 + (${de})` : (y, de) => `y0 - (${de}) < ${y}`;
    const Q = dir === 'up' ? y => `${G}[${y}] < ${x0} + eps` : y => `${x0} - eps < ${G}[${y}]`;
    const fin = (cc, de, der, dep, allY) => X.exI(X.tc(cc, [der, dep, allY], `${de} in Real & 0 < ${de} & all y. (y in dom(${G}) -> ${R('y', de)} -> ${Q('y')})`),
      'de', `de in Real & 0 < de & all y. (y in dom(${G}) -> ${R('y', 'de')} -> ${Q('y')})`, de);
    const caseA = (hE, cA) => X.exE(hE, 'u', (hu, cu) => {
      const ud = X.tc(cu, [hu], 'u in dom(f)'), ur = domR(cu, hR, 'f', 'u', ud);
      const ulx = X.tc(cu, [hu], dir === 'up' ? `${x0} < u` : `u < ${x0}`);
      const gap = dir === 'up' ? `u - ${x0}` : `${x0} - u`;
      const gp = dir === 'up' ? use('SubPos', [x0, 'u'], cu, [x0r, ur, ulx]) : use('SubPos', ['u', x0], cu, [x0r, ur, ulx]);
      return X.exE(use('MinPos', [gap, 'eps'], cu, [ur, x0r, gp, hp]), 'd', (hd, cd) => {
        const dr = X.tc(cd, [hd], 'd in Real'), dp = X.tc(cd, [hd], '0 < d'), dg = X.tc(cd, [hd], `d <= ${gap}`), de_ = X.tc(cd, [hd], 'd <= eps');
        const f = [dr, x0r, ur, y0r];
        let x1, x1in, near, x1lt;
        if (dir === 'up') {
          x1 = `${x0} + d`;
          near = use('LtAddPos', [x0, 'd'], cd, [dp, ...f]);  // x0 < x1
          const l = use('LeAddRight', ['d', gap, x0], cd, [dg, ...f]);
          const l2 = X.rw(use('SubAdd', ['u', x0], cd, f), l, `d + ${x0} <= u`, cd);
          const x1u = X.rw(use('R3', ['d', x0], cd, f), l2, `${x1} <= u`, cd);
          x1in = itv(cd, hI, 'dom(f)', x0, x1, 'u', x0d, ud, mem(cd, x1, f), X.tc(cd, [near], `${x0} <= ${x1}`), x1u);
          x1lt = use('AddLeLe', [x0, x0, 'd', 'eps'], cd, [X.tc(cd, [X.refl(x0)], `${x0} <= ${x0}`), de_, ...f]); // x1 <= x0 + eps
        } else {
          x1 = `${x0} - d`;
          near = use('SubLtSelf', [x0, 'd'], cd, [dp, ...f]);  // x1 < x0
          const l = use('SubLeAnti', [x0, 'd', gap], cd, [dg, ...f]);  // x0 - (x0 - u) <= x0 - d
          const ux1 = X.rw(use('SubSubSelf', [x0, 'u'], cd, f), l, `u <= ${x1}`, cd);
          x1in = itv(cd, hI, 'dom(f)', 'u', x1, x0, ud, x0d, mem(cd, x1, f), ux1, X.tc(cd, [near], `${x1} <= ${x0}`));
          x1lt = use('SubLeAnti', [x0, 'd', 'eps'], cd, [de_, ...f]); // x0 - eps <= x1
        }
        const fx1 = `f[${x1}]`;
        const fr = use('RFnVal', ['f', x1], cd, [hR, x1in]);
        const flt0 = dir === 'up' ? inc(cd, hS, 'f', 'dom(f)', x0, x1, x0d, x1in, near) : inc(cd, hS, 'f', 'dom(f)', x1, x0, x1in, x0d, near);
        const flt = X.rw(fx0, flt0, dir === 'up' ? `y0 < ${fx1}` : `${fx1} < y0`, cd);
        const de = dir === 'up' ? `${fx1} - y0` : `y0 - ${fx1}`;
        const dep = dir === 'up' ? use('SubPos', ['y0', fx1], cd, [y0r, fr, flt]) : use('SubPos', [fx1, 'y0'], cd, [y0r, fr, flt]);
        const der = mem(cd, de, [y0r, fr]);
        const bnd = dir === 'up' ? calc(cd, `y0 + (${de})`, [[`(${de}) + y0`, use('R3', ['y0', de], cd, [y0r, der])], [fx1, use('SubAdd', [fx1, 'y0'], cd, [fr, y0r])]])
          : use('SubSubSelf', ['y0', fx1], cd, [y0r, fr]);
        const fxd = inDomG(cd, inv, x1, x1in);
        const gfx = invFx(cd, inv, x1, x1in);
        const allY = X.gen(X.assume(cd, `y in dom(${G})`, (hy, cy) => X.assume(cy, R('y', de), (hr, cr) => {
          if (dir === 'up') {
            const l = X.rw(bnd, hr, `y < ${fx1}`, cr);
            const g1 = X.rw(gfx, inc(cr, gS, G, `dom(${G})`, 'y', fx1, hy, fxd, l), `${G}[y] < ${x1}`, cr);
            return use('LtLeTrans', [`${G}[y]`, x1, `${x0} + eps`], cr, [g1, x1lt]);
          }
          const l = X.rw(bnd, hr, `${fx1} < y`, cr);
          const g1 = X.rw(gfx, inc(cr, gS, G, `dom(${G})`, fx1, 'y', fxd, hy, l), `${x1} < ${G}[y]`, cr);
          return use('LeLtTrans', [`${x0} - eps`, x1, `${G}[y]`], cr, [x1lt, g1]);
        })), 'y');
        return fin(cd, de, der, dep, allY);
      }, cu);
    }, cA);
    const caseB = (hn, cB) => {
      const one = X.thm('R1_1'), op = X.thm('ZeroLtOne');
      const allY = X.gen(X.assume(cB, `y in dom(${G})`, (hy, cy) => X.assume(cy, R('y', '1'), (hr, cr) => {
        const [gd] = invAt(cr, inv, 'y', hy);
        const gy = `${G}[y]`, gr = domR(cr, hR, 'f', gy, gd);
        const lt = dir === 'up' ? `${x0} < ${gy}` : `${gy} < ${x0}`;
        const imp = X.assume(cr, lt, (h, c2) => X.exI(X.tc(c2, [gd, h], dir === 'up' ? `${gy} in dom(f) & ${x0} < ${gy}` : `${gy} in dom(f) & ${gy} < ${x0}`),
          'u', dir === 'up' ? `u in dom(f) & ${x0} < u` : `u in dom(f) & u < ${x0}`, gy));
        const nl = X.tc(cr, [hn, imp], `~ ${lt}`);
        if (dir === 'up') {
          const le = use('NotLtLe', [x0, gy], cr, [x0r, gr, nl]);
          return use('LeLtTrans', [gy, x0, `${x0} + eps`], cr, [le, use('LtAddPos', [x0, 'eps'], cr, [x0r, hp])]);
        }
        const le = use('NotLtLe', [gy, x0], cr, [gr, x0r, nl]);
        return use('LtLeTrans', [`${x0} - eps`, x0, gy], cr, [use('SubLtSelf', [x0, 'eps'], cr, [x0r, hp]), le]);
      })), 'y');
      return fin(cB, '1', one, op, allY);
    };
    return K.cases(c, X.tc(c, [], `(${E}) | ~ (${E})`), [caseA, caseB], goal);
  }), ['f', 'y0', 'eps']);
}
const sideStmt = g => `all f. all y0. all eps. (${[...H3, `y0 in dom(${G})`, 'eps in Real', '0 < eps'].join(' -> ')} -> ${g})`;
prove('InvUp', sideStmt(up), '[I3]', sideProof('up'));
prove('InvDown', sideStmt(down), '[I4]', sideProof('down'));

// ---------------- 定理2.21 ----------------
prove('InvCont', `all f. (RFn(f) -> Itv(dom(f)) -> StrInc(f, dom(f)) -> ContOn(${G}, dom(${G})))`, '定理2.21(連続性)', () => X.gen(hyps(H3, (c, [hR, hI, hS]) => {
  const { inv, gR } = setup(c, hR, hS);
  const A = `dom(${G})`;
  const sub = X.inst(X.thm('SubRefl'), [T(A)]);
  const allC = X.gen(X.assume(c, `y0 in ${A}`, (hy0, c1) => {
    const x0 = `${G}[y0]`;
    const [x0d] = invAt(c1, inv, 'y0', hy0);
    const x0r = domR(c1, hR, 'f', x0, x0d);
    const y0r = domR(c1, gR, G, 'y0', hy0);
    const allE = X.gen(X.assume(c1, 'eps in Real', (he, c2) => X.assume(c2, '0 < eps', (hp, c3) => {
      const ups = use('InvUp', ['f', 'y0', 'eps'], c3, [hR, hI, hS, hy0, he, hp]);
      const dns = use('InvDown', ['f', 'y0', 'eps'], c3, [hR, hI, hS, hy0, he, hp]);
      return X.exE(ups, 'd1', (h1, c4) => X.exE(dns, 'd2', (h2, c5) => {
        const d1r = X.tc(c5, [h1], 'd1 in Real'), d2r = X.tc(c5, [h2], 'd2 in Real');
        return X.exE(use('MinPos', ['d1', 'd2'], c5, [d1r, d2r, X.tc(c5, [h1], '0 < d1'), X.tc(c5, [h2], '0 < d2')]), 'de', (hd, c6) => {
          const dr = X.tc(c6, [hd], 'de in Real'), dp = X.tc(c6, [hd], '0 < de');
          const f = [dr, d1r, d2r, y0r];
          const le1 = use('AddLeLe', ['y0', 'y0', 'de', 'd1'], c6, [X.tc(c6, [X.refl('y0')], 'y0 <= y0'), X.tc(c6, [hd], 'de <= d1'), ...f]);
          const le2 = use('SubLeAnti', ['y0', 'de', 'd2'], c6, [X.tc(c6, [hd], 'de <= d2'), ...f]);
          const allX = X.gen(X.assume(c6, `x in ${A}`, (hx, c7) => X.assume(c7, 'abs(x - y0) < de', (ha, c8) => {
            const xr = domR(c8, gR, G, 'x', hx);
            const bo = use('AbsLtBoth', ['x', 'y0', 'de'], c8, [xr, ...f, ha]);
            const xu = use('LtLeTrans', ['x', 'y0 + de', 'y0 + d1'], c8, [X.tc(c8, [bo], 'x < y0 + de'), le1]);
            const xl = use('LeLtTrans', ['y0 - d2', 'y0 - de', 'x'], c8, [le2, X.tc(c8, [bo], 'y0 - de < x')]);
            const g1 = X.tc(c8, [X.inst(X.tc(c8, [h1], `all y. (y in ${A} -> y < y0 + d1 -> ${G}[y] < ${x0} + eps)`), [T('x')]), hx, xu], `${G}[x] < ${x0} + eps`);
            const g2 = X.tc(c8, [X.inst(X.tc(c8, [h2], `all y. (y in ${A} -> y0 - d2 < y -> ${x0} - eps < ${G}[y])`), [T('x')]), hx, xl], `${x0} - eps < ${G}[x]`);
            const [gxd] = invAt(c8, inv, 'x', hx);
            const gxr = domR(c8, hR, 'f', `${G}[x]`, gxd);
            const ff = [gxr, x0r, he];
            return use('LtAbs', [`${G}[x] - ${x0}`, 'eps'], c8, [use('SubLtSwap', [x0, 'eps', `${G}[x]`], c8, [...ff, g2]), use('LtAddSwap', [x0, 'eps', `${G}[x]`], c8, [...ff, g1]), ...ff]);
          })), 'x');
          const G2 = de => `${de} in Real & 0 < ${de} & all x. (x in ${A} -> abs(x - y0) < ${de} -> abs(${G}[x] - ${G}[y0]) < eps)`;
          return X.exI(X.tc(c6, [dr, dp, allX], G2('de')), 'de', G2('de'), 'de');
        }, c5);
      }, c4), c3);
    })), 'eps');
    return X.tc(c1, [X.inst(X.defAx('ContIn'), [T(G), T(A), T('y0')]), gR, sub, hy0, allE], `ContIn(${G}, ${A}, y0)`);
  }), 'y0');
  return X.tc(c, [X.inst(X.defAx('ContOn'), [T(G), T(A)]), gR, sub, allC], `ContOn(${G}, ${A})`);
}), 'f'));

prove('InvItv', `all f. (ContOn(f, dom(f)) -> Itv(dom(f)) -> StrInc(f, dom(f)) -> Itv(dom(${G})))`, '定理2.21(定義域)', () => X.gen(hyps(['ContOn(f, dom(f))', 'Itv(dom(f))', 'StrInc(f, dom(f))'], (c, [hC, hI, hS]) => {
  const hR = X.tc(c, [hC, X.inst(X.defAx('ContOn'), [T('f'), T('dom(f)')])], 'RFn(f)');
  const { inv, gR } = setup(c, hR, hS);
  const gS = use('InvMono', ['f'], c, [hR, hS]);
  const A = `dom(${G})`;
  const subR = X.tc(c, [X.inst(X.defAx('sub'), [T(A), T('Real')]), X.gen(X.assume(c, `u in ${A}`, (hu, cu) => domR(cu, gR, G, 'u', hu)), 'u')], `${A} sub Real`);
  const body = X.assume(c, `x in ${A}`, (hx, c1) => X.assume(c1, `z in ${A}`, (hz, c2) => X.assume(c2, 'y in Real', (hy, c3) => X.assume(c3, 'x <= y', (h1, c4) => X.assume(c4, 'y <= z', (h2, c5) => {
    const goal = `y in ${A}`;
    return K.cases(c5, X.tc(c5, [h1], 'x < y | x = y'), [
      (hxy, c6) => K.cases(c6, X.tc(c6, [h2], 'y < z | y = z'), [
        (hyz, c7) => {
          const a = `${G}[x]`, b = `${G}[z]`;
          const [ad, fa] = invAt(c7, inv, 'x', hx), [bd, fb] = invAt(c7, inv, 'z', hz);
          const ar = domR(c7, hR, 'f', a, ad), br = domR(c7, hR, 'f', b, bd);
          const ab = inc(c7, gS, G, A, 'x', 'z', hx, hz, use('LtTrans', ['x', 'y', 'z'], c7, [hxy, hyz]));
          const I = `cint(${a},${b})`;
          const inI = (cc, t, ht) => { // t ∈ [a,b] → t ∈ dom f
            const dc = X.tc(cc, [ht, X.inst(X.defAx('cint'), [T(a), T(b), T(t)])], `${t} in Real & ${a} <= ${t} & ${t} <= ${b}`);
            return itv(cc, hI, 'dom(f)', a, t, b, ad, bd, X.tc(cc, [dc], `${t} in Real`), X.tc(cc, [dc], `${a} <= ${t}`), X.tc(cc, [dc], `${t} <= ${b}`));
          };
          const subI = X.tc(c7, [X.inst(X.defAx('sub'), [T(I), T('dom(f)')]), X.gen(X.assume(c7, `t in ${I}`, (ht, ct) => inI(ct, 't', ht)), 't')], `${I} sub dom(f)`);
          const allCI = X.gen(X.assume(c7, `t in ${I}`, (ht, ct) => {
            const cin = X.tc(ct, [X.inst(X.tc(ct, [hC, X.inst(X.defAx('ContOn'), [T('f'), T('dom(f)')])], 'all c. (c in dom(f) -> ContIn(f, dom(f), c))'), [T('t')]), inI(ct, 't', ht)], 'ContIn(f, dom(f), t)');
            return use('ContInSub', ['f', 'dom(f)', I, 't'], ct, [cin, subI, ht]);
          }), 't');
          const co = X.tc(c7, [X.inst(X.defAx('ContOn'), [T('f'), T(I)]), hR, subI, X.alphaConv(allCI, `all c. (c in ${I} -> ContIn(f, ${I}, c))`)], `ContOn(f, ${I})`);
          const lo = X.rw(X.sym(fa), hxy, `f[${a}] < y`, c7), hi = X.rw(X.sym(fb), hyz, `y < f[${b}]`, c7);
          return X.exE(use('IVT', ['f', a, b, 'y'], c7, [co, ar, br, hy, ab, lo, hi]), 'xi', (hxi, c8) => {
            const xr = X.tc(c8, [hxi], 'xi in Real');
            const xI = X.tc(c8, [X.inst(X.defAx('cint'), [T(a), T(b), T('xi')]), xr, X.tc(c8, [hxi], `${a} < xi`), X.tc(c8, [hxi], `xi < ${b}`)], `xi in ${I}`);
            const xd = inI(c8, 'xi', xI);
            return X.rw(X.tc(c8, [hxi], 'f[xi] = y'), inDomG(c8, inv, 'xi', xd), goal, c8);
          }, c7);
        },
        (hyz, c7) => X.rw(X.sym(hyz), hz, goal, c7)], goal),
      (hxy, c6) => X.rw(hxy, hx, goal, c6)], goal);
  })))));
  return X.tc(c, [X.inst(X.defAx('Itv'), [T(A)]), subR, X.genAll(body, ['x', 'y', 'z'])], `Itv(${A})`);
}), 'f'));
