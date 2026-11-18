'use strict';
// テキスト第4章 1節: 関数の極限
const K = require('./kit');
const { X, prove, intro, use, calc, mem } = K;
require('./p_ch3');

const flimDef = (f, c, al) => X.inst(X.defAx('FLim'), [f, c, al]);
const DF = (f, c, al, e) => `ex de. (de in Real & 0 < de & all x. (x in dom(${f}) -> 0 < abs(x - ${c}) -> abs(x - ${c}) < de -> abs(${f}[x] - ${al}) < ${e}))`;

prove('FLimE', `all f. all c. all al. all eps. (FLim(f,c,al) -> eps in Real -> 0 < eps -> ${DF('f', 'c', 'al', 'eps')})`, '[D1]', () => X.genAll(
  X.assume([], 'FLim(f,c,al)', (h, c1) => X.assume(c1, 'eps in Real', (he, c2) => X.assume(c2, '0 < eps', (hp, c) => {
    const all = X.tc(c, [h, flimDef('f', 'c', 'al')], `all eps. (eps in Real -> 0 < eps -> ${DF('f', 'c', 'al', 'eps')})`);
    return X.tc(c, [X.inst(all, ['eps']), he, hp], DF('f', 'c', 'al', 'eps'));
  }))), ['f', 'c', 'al', 'eps']));
for (const [nm, part, lab] of [['FLimRFn', 'RFn(f)', '[D2]'], ['FLimCR', 'c in Real', '[D3]'], ['FLimAR', 'al in Real', '[D4]'], ['FLimNb', 'PNbhd(f,c)', '[D5]']])
  prove(nm, `all f. all c. all al. (FLim(f,c,al) -> ${part})`, lab, () => X.genAll(X.assume([], 'FLim(f,c,al)', (h, cc) => X.tc(cc, [h, flimDef('f', 'c', 'al')], part)), ['f', 'c', 'al']));

// |x| = 0 → x = 0
prove('AbsZeroEq', 'all x. (x in Real -> abs(x) = 0 -> x = 0)', '[D6]', () => intro(['x'], ['abs(x) = 0'], (c, [h]) => X.raa(c, 'x = 0', (hn, c2) => {
  const p = use('AbsPos', ['x'], c2, [hn]);
  return [X.rw(h, p, '0 < 0', c2), X.inst(X.thm('LtIrrefl'), ['0'])];
})));
prove('SubZeroEq', 'all x. all y. (x in Real -> y in Real -> x - y = 0 -> x = y)', '[D7]', () => intro(['x', 'y'], ['x - y = 0'], (c, [h]) =>
  calc(c, 'x', [['(x - y) + y', X.sym(use('SubAdd', ['x', 'y'], c))], ['0 + y', h], ['y + 0', use('R3', ['0', 'y'], c)], ['y', use('R4', ['y'], c)]])));

// 2つの正数より小さい正数の存在
prove('MinPos', 'all p. all q. (p in Real -> q in Real -> 0 < p -> 0 < q -> ex d. (d in Real & 0 < d & d <= p & d <= q))', '[D8]', () =>
  intro(['p', 'q'], ['0 < p', '0 < q'], (c, [hp, hq]) => {
    const G = 'd in Real & 0 < d & d <= p & d <= q';
    const r = use('R13', ['p', 'q'], c);
    const lp = X.assume(c, 'p < q', (h, c2) => X.exI(X.tc(c2, [hp, h, X.refl('p'), X.hyp(c2, 0)], 'p in Real & 0 < p & p <= p & p <= q'), 'd', G, 'p'));
    const ep = X.assume(c, 'p = q', (h, c2) => X.exI(X.tc(c2, [hp, h, X.refl('p'), X.hyp(c2, 0)], 'p in Real & 0 < p & p <= p & p <= q'), 'd', G, 'p'));
    const lq = X.assume(c, 'q < p', (h, c2) => X.exI(X.tc(c2, [hq, h, X.refl('q'), X.hyp(c2, 1)], 'q in Real & 0 < q & q <= p & q <= q'), 'd', G, 'q'));
    return X.tc(c, [r, lp, ep, lq], `ex d. (${G})`);
  }));

// ---------- 定理 1.7 (⇒): 関数の極限と数列の極限 ----------
prove('SeqCrit', 'all f. all c. all al. all a. (FLim(f,c,al) -> Conv(a,c) -> (all n. (n in Nat -> a[n] in dom(f) & a[n] != c)) -> Conv(compseq(f,a), al))', '定理1.7(⇒)', () => X.genAll(
  X.assume([], 'FLim(f,c,al)', (hf, k1) => X.assume(k1, 'Conv(a,c)', (ha, k2) => X.assume(k2, 'all n. (n in Nat -> a[n] in dom(f) & a[n] != c)', (hd, k) => {
    const rf = use('FLimRFn', ['f', 'c', 'al'], k, [hf]), cr = use('FLimCR', ['f', 'c', 'al'], k, [hf]), ar = use('FLimAR', ['f', 'c', 'al'], k, [hf]);
    const sa = use('ConvSeq', ['a', 'c'], k, [ha]);
    const dom = X.gen(X.assume(k, 'n in Nat', (hn, kn) => X.tc(kn, [X.inst(hd, ['n']), hn], 'a[n] in dom(f)')), 'n');
    const cs = use('CompSeq', ['f', 'a'], k, [rf, sa, dom]);
    const seq = X.tc(k, [cs], 'Seq(compseq(f,a))');
    const val = X.tc(k, [cs], 'all n. (n in Nat -> compseq(f,a)[n] = f[a[n]])');
    const all = X.gen(X.assume(k, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => {
      const fd = use('FLimE', ['f', 'c', 'al', 'eps'], c2, [hf, he, hp]);
      return X.exE(fd, 'de', (hde, cd) => {
        const der = X.tc(cd, [hde], 'de in Real'), dep = X.tc(cd, [hde], '0 < de');
        const fall = X.tc(cd, [hde], 'all x. (x in dom(f) -> 0 < abs(x - c) -> abs(x - c) < de -> abs(f[x] - al) < eps)');
        const ce = use('ConvE', ['a', 'c', 'de'], cd, [ha, der, dep]);
        return X.exE(ce, 'N', (hN, cN) => {
          const aall = X.tc(cN, [hN], 'all n. (n in Nat -> N <= n -> abs(a[n] - c) < de)');
          const body = X.assume(cN, 'n in Nat', (hn, cn) => X.assume(cn, 'N <= n', (hl, cl) => {
            const dn = X.tc(cl, [X.inst(hd, ['n']), hn], 'a[n] in dom(f) & a[n] != c');
            const xr = mem(cl, 'a[n]', [sa, hn]);
            const pos = use('AbsPos', ['a[n] - c'], cl, [use('SubNeZero', ['a[n]', 'c'], cl, [xr, cr, X.tc(cl, [dn], 'a[n] != c')]), xr, cr]);
            const lt = X.tc(cl, [X.inst(aall, ['n']), hn, hl], 'abs(a[n] - c) < de');
            const fv = X.tc(cl, [X.inst(fall, ['a[n]']), dn, pos, lt], 'abs(f[a[n]] - al) < eps');
            return X.rw(X.sym(X.tc(cl, [X.inst(val, ['n']), hn], 'compseq(f,a)[n] = f[a[n]]')), fv, 'abs(compseq(f,a)[n] - al) < eps', cl);
          }));
          const G = 'N in Nat & all n. (n in Nat -> N <= n -> abs(compseq(f,a)[n] - al) < eps)';
          return X.exI(X.tc(cN, [X.tc(cN, [hN], 'N in Nat'), X.gen(body, 'n')], G), 'N', G, 'N');
        });
      });
    })), 'eps');
    return X.tc(k, [X.inst(X.defAx('Conv'), ['compseq(f,a)', 'al']), seq, ar, all], 'Conv(compseq(f,a), al)');
  }))), ['f', 'c', 'al', 'a']));

// ---------- 定理 1.11: 合成関数の極限 ----------
prove('FLimComp', 'all f. all g. all c. all b. (FLim(f,c,b) -> FLim(g,b,g[b]) -> b in dom(g) -> PNbhd(comp(g,f),c) -> FLim(comp(g,f), c, g[b]))', '定理1.11', () => X.genAll(
  X.assume([], 'FLim(f,c,b)', (hf, k1) => X.assume(k1, 'FLim(g,b,g[b])', (hg, k2) => X.assume(k2, 'b in dom(g)', (hb, k3) => X.assume(k3, 'PNbhd(comp(g,f),c)', (hn, k) => {
    const rf = use('FLimRFn', ['f', 'c', 'b'], k, [hf]), rg = use('FLimRFn', ['g', 'b', 'g[b]'], k, [hg]);
    const cr = use('FLimCR', ['f', 'c', 'b'], k, [hf]), br = use('FLimAR', ['f', 'c', 'b'], k, [hf]);
    const gb = mem(k, 'g[b]', [rg, hb]);
    const cf = use('CompFn', ['g', 'f'], k, [rg, rf]);
    const rc = X.tc(k, [cf], 'RFn(comp(g,f))');
    const cval = X.tc(k, [cf], 'all x. (x in dom(comp(g,f)) -> x in dom(f) & f[x] in dom(g) & comp(g,f)[x] = g[f[x]])');
    const all = X.gen(X.assume(k, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => {
      const gd = use('FLimE', ['g', 'b', 'g[b]', 'eps'], c2, [hg, he, hp]);
      return X.exE(gd, 'dg', (hd1, d1) => {
        const d1r = X.tc(d1, [hd1], 'dg in Real'), d1p = X.tc(d1, [hd1], '0 < dg');
        const gall = X.tc(d1, [hd1], 'all x. (x in dom(g) -> 0 < abs(x - b) -> abs(x - b) < dg -> abs(g[x] - g[b]) < eps)');
        // y = b の場合も含めて: y ∈ dom g, |y - b| < δ1 → |g(y) - g(b)| < ε
        const gext = X.gen(X.assume(d1, 'y in dom(g)', (hy, cy) => X.assume(cy, 'abs(y - b) < dg', (hyl, cyl) => {
          const yr = use('RFnDom', ['g', 'y'], cyl, [rg, hy]);
          const nn = use('AbsNonneg', ['y - b'], cyl, [yr, br]);
          const z = X.assume(cyl, '0 = abs(y - b)', (h0, cz) => {
            const yb = use('SubZeroEq', ['y', 'b'], cz, [use('AbsZeroEq', ['y - b'], cz, [X.sym(h0), yr, br]), yr, br]);
            const s = calc(cz, 'abs(g[y] - g[b])', [['abs(g[b] - g[b])', yb], ['abs(0)', use('SubSelf', ['g[b]'], cz, [gb])], ['0', use('AbsOfNonneg', ['0'], cz, [X.tc(cz, [X.refl('0')], '0 <= 0')])]]);
            return X.rw(X.sym(s), hp, 'abs(g[y] - g[b]) < eps', cz);
          });
          return X.tc(cyl, [nn, z, X.inst(gall, ['y']), hy, hyl], 'abs(g[y] - g[b]) < eps');
        })), 'y');
        const fd = use('FLimE', ['f', 'c', 'b', 'dg'], d1, [hf, d1r, d1p]);
        return X.exE(fd, 'de2', (hd2, d2) => {
          const fall = X.tc(d2, [hd2], 'all x. (x in dom(f) -> 0 < abs(x - c) -> abs(x - c) < de2 -> abs(f[x] - b) < dg)');
          const body = X.gen(X.assume(d2, 'x in dom(comp(g,f))', (hx, cx) => X.assume(cx, '0 < abs(x - c)', (h1, cx1) => X.assume(cx1, 'abs(x - c) < de2', (h2, cx2) => {
            const v = X.tc(cx2, [X.inst(cval, ['x']), hx], 'x in dom(f) & f[x] in dom(g) & comp(g,f)[x] = g[f[x]]');
            const fl = X.tc(cx2, [X.inst(fall, ['x']), v, h1, h2], 'abs(f[x] - b) < dg');
            const gl = X.tc(cx2, [X.inst(gext, ['f[x]']), v, fl], 'abs(g[f[x]] - g[b]) < eps');
            return X.rw(X.sym(X.tc(cx2, [v], 'comp(g,f)[x] = g[f[x]]')), gl, 'abs(comp(g,f)[x] - g[b]) < eps', cx2);
          }))), 'x');
          const G = 'de in Real & 0 < de & all x. (x in dom(comp(g,f)) -> 0 < abs(x - c) -> abs(x - c) < de -> abs(comp(g,f)[x] - g[b]) < eps)';
          return X.exI(X.tc(d2, [hd2, body], G.replace(/de\b/g, 'de2')), 'de', G, 'de2');
        }, d1);
      }, c2);
    })), 'eps');
    return X.tc(k, [X.inst(X.defAx('FLim'), ['comp(g,f)', 'c', 'g[b]']), rc, cr, gb, hn, all], 'FLim(comp(g,f), c, g[b])');
  })))), ['f', 'g', 'c', 'b']));

// ---------- 定理 1.10: はさみうち法 ----------
const SQH = 'all x. (x in dom(h) -> 0 < abs(x - c) -> abs(x - c) < r -> x in dom(f) & x in dom(g) & f[x] <= h[x] & h[x] <= g[x])';
prove('FSqueeze', `all f. all g. all h. all c. all al. all r. (FLim(f,c,al) -> FLim(g,c,al) -> RFn(h) -> PNbhd(h,c) -> r in Real -> 0 < r -> (${SQH}) -> FLim(h,c,al))`, '定理1.10', () => X.genAll(
  X.assume([], 'FLim(f,c,al)', (hf, k1) => X.assume(k1, 'FLim(g,c,al)', (hg, k2) => X.assume(k2, 'RFn(h)', (rh, k3) => X.assume(k3, 'PNbhd(h,c)', (hnb, k4) =>
    X.assume(k4, 'r in Real', (rr, k5) => X.assume(k5, '0 < r', (rp, k6) => X.assume(k6, SQH, (hs, k) => {
      const rf = use('FLimRFn', ['f', 'c', 'al'], k, [hf]), rg = use('FLimRFn', ['g', 'c', 'al'], k, [hg]);
      const cr = use('FLimCR', ['f', 'c', 'al'], k, [hf]), ar = use('FLimAR', ['f', 'c', 'al'], k, [hf]);
      const all = X.gen(X.assume(k, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => {
        const fd = use('FLimE', ['f', 'c', 'al', 'eps'], c2, [hf, he, hp]);
        return X.exE(fd, 'd1', (h1, e1) => {
          const gd = use('FLimE', ['g', 'c', 'al', 'eps'], e1, [hg, he, hp]);
          return X.exE(gd, 'd2', (h2, e2) => {
            const m12 = use('MinPos', ['d1', 'd2'], e2, [X.tc(e2, [h1], 'd1 in Real'), X.tc(e2, [h2], 'd2 in Real'), X.tc(e2, [h1], '0 < d1'), X.tc(e2, [h2], '0 < d2')]);
            return X.exE(m12, 'd3', (h3, e3) => {
              const m = use('MinPos', ['d3', 'r'], e3, [X.tc(e3, [h3], 'd3 in Real'), rr, X.tc(e3, [h3], '0 < d3'), rp]);
              return X.exE(m, 'de', (hd, e4) => {
                const fall = X.tc(e4, [h1], 'all x. (x in dom(f) -> 0 < abs(x - c) -> abs(x - c) < d1 -> abs(f[x] - al) < eps)');
                const gall = X.tc(e4, [h2], 'all x. (x in dom(g) -> 0 < abs(x - c) -> abs(x - c) < d2 -> abs(g[x] - al) < eps)');
                const body = X.gen(X.assume(e4, 'x in dom(h)', (hx, cx) => X.assume(cx, '0 < abs(x - c)', (p1, cx1) => X.assume(cx1, 'abs(x - c) < de', (p2, cx2) => {
                  const xr = use('RFnDom', ['h', 'x'], cx2, [rh, hx]);
                  const ad = mem(cx2, 'abs(x - c)', [xr, cr]);
                  const lt = (d, hdl) => use('LtLeTrans', ['abs(x - c)', 'de', d], cx2, [p2, hdl]);
                  const lt3 = lt('d3', X.tc(cx2, [hd], 'de <= d3'));
                  const ltr = lt('r', X.tc(cx2, [hd], 'de <= r'));
                  const lt1 = use('LtLeTrans', ['abs(x - c)', 'd3', 'd1'], cx2, [lt3, X.tc(cx2, [h3], 'd3 <= d1')]);
                  const lt2 = use('LtLeTrans', ['abs(x - c)', 'd3', 'd2'], cx2, [lt3, X.tc(cx2, [h3], 'd3 <= d2')]);
                  const sh = X.tc(cx2, [X.inst(hs, ['x']), hx, p1, ltr], 'x in dom(f) & x in dom(g) & f[x] <= h[x] & h[x] <= g[x]');
                  const fe = X.tc(cx2, [X.inst(fall, ['x']), sh, p1, lt1], 'abs(f[x] - al) < eps');
                  const ge = X.tc(cx2, [X.inst(gall, ['x']), sh, p1, lt2], 'abs(g[x] - al) < eps');
                  const fv = use('RFnVal', ['f', 'x'], cx2, [rf, X.tc(cx2, [sh], 'x in dom(f)')]);
                  const gv = use('RFnVal', ['g', 'x'], cx2, [rg, X.tc(cx2, [sh], 'x in dom(g)')]);
                  const hv = use('RFnVal', ['h', 'x'], cx2, [rh, hx]);
                  return use('ErrSqueeze', ['f[x]', 'g[x]', 'h[x]', 'al', 'eps'], cx2, [fv, gv, hv, ar, he, X.tc(cx2, [sh], 'f[x] <= h[x]'), X.tc(cx2, [sh], 'h[x] <= g[x]'), fe, ge]);
                }))), 'x');
                const G = 'de in Real & 0 < de & all x. (x in dom(h) -> 0 < abs(x - c) -> abs(x - c) < de -> abs(h[x] - al) < eps)';
                return X.exI(X.tc(e4, [hd, body], G), 'de', G, 'de');
              }, e3);
            }, e2);
          }, e1);
        }, c2);
      })), 'eps');
      return X.tc(k, [X.inst(X.defAx('FLim'), ['h', 'c', 'al']), rh, cr, ar, hnb, all], 'FLim(h,c,al)');
    }))))))), ['f', 'g', 'h', 'c', 'al', 'r']));

module.exports = {};
