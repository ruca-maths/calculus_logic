'use strict';
// 第3章・第4章 (ZFC): 空集合, 数学的帰納法
const K = require('./kit');
const { X, prove } = K;

// 空集合の存在
prove('EmptyEx', 'ex y. all u. u notin y', '定理(空集合の存在)', () => {
  const sep = X.axiom('Sep', 'all a. ex y. all u. (u in y <-> u in a & u != u)');
  return X.exE(X.inst(sep, ['a']), 'y', (h, c) => {
    const nu = X.tc(c, [X.inst(h, ['u']), X.refl('u')], 'u notin y');
    return X.exI(X.gen(nu, 'u'), 'y', 'all u. u notin y', 'y');
  });
});
// 空集合の一意性
prove('EmptyUnique', 'all y. all y2. ((all u. u notin y) -> (all u. u notin y2) -> y = y2)', '定理(空集合の一意性)', () => X.genAll(
  X.assume([], 'all u. u notin y', (h1, c1) => X.assume(c1, 'all u. u notin y2', (h2, c) => {
    const iff = X.tc(c, [X.inst(h1, ['u']), X.inst(h2, ['u'])], 'u in y <-> u in y2');
    return X.tc(c, [X.inst(X.axiom('Ext'), ['y', 'y2']), X.gen(iff, 'u')], 'y = y2');
  })), ['y', 'y2']));

// ω は帰納的
prove('OmegaInd', 'Ind(omega)', '補題(ωは帰納的)', () => {
  const dO = n => X.inst(X.defAx('omega'), [n]);
  const dI = x => X.inst(X.defAx('Ind'), [x]);
  const e = X.gen(X.assume([], 'Ind(x)', (h, c) => X.tc(c, [h, dI('x')], 'emptyset in x')), 'x');
  const z = X.tc([], [dO('emptyset'), e], 'emptyset in omega');
  const s = X.gen(X.assume([], 'n in omega', (hn, c) => {
    const all = X.tc(c, [hn, dO('n')], 'all x. (Ind(x) -> n in x)');
    const g = X.gen(X.assume(c, 'Ind(x)', (h, c2) => {
      const nx = X.tc(c2, [X.inst(all, ['x']), h], 'n in x');
      const cl = X.tc(c2, [h, dI('x')], 'all y. (y in x -> S(y) in x)');
      return X.tc(c2, [X.inst(cl, ['n']), nx], 'S(n) in x');
    }), 'x');
    return X.tc(c, [g, dO('S(n)')], 'S(n) in omega');
  }), 'n');
  return X.tc([], [dI('omega'), z, s], 'Ind(omega)');
});

// 数学的帰納法 (図式. Φ は任意の論理式 φ(n) を表す図式文字)
prove('Induction', 'Phi(emptyset) -> (all n. (n in omega -> Phi(n) -> Phi(S(n)))) -> all n. (n in omega -> Phi(n))', '定理(数学的帰納法)', () =>
  X.assume([], 'Phi(emptyset)', (h0, c1) => X.assume(c1, 'all n. (n in omega -> Phi(n) -> Phi(S(n)))', (hs, c) => {
    const sep = X.axiom('Sep', 'all a. ex y. all x. (x in y <-> x in a & Phi(x))');
    return X.exE(X.inst(sep, ['omega']), 'B', (hB, cB) => {
      const dB = x => X.inst(hB, [x]);
      const oi = X.tc(cB, [X.thm('OmegaInd'), X.inst(X.defAx('Ind'), ['omega'])], 'emptyset in omega & all y. (y in omega -> S(y) in omega)');
      const zB = X.tc(cB, [dB('emptyset'), oi, h0], 'emptyset in B');
      const sB = X.gen(X.assume(cB, 'y in B', (hy, cy) => {
        const yy = X.tc(cy, [dB('y'), hy], 'y in omega & Phi(y)');
        return X.tc(cy, [yy, X.inst(hs, ['y']), X.inst(X.tc(cy, [oi], 'all y. (y in omega -> S(y) in omega)'), ['y']), dB('S(y)')], 'S(y) in B');
      }), 'y');
      const indB = X.tc(cB, [X.inst(X.defAx('Ind'), ['B']), zB, sB], 'Ind(B)');
      return X.gen(X.assume(cB, 'n in omega', (hn, cn) => {
        const all = X.tc(cn, [hn, X.inst(X.defAx('omega'), ['n'])], 'all x. (Ind(x) -> n in x)');
        return X.tc(cn, [X.inst(all, ['B']), indB, dB('n')], 'Phi(n)');
      }), 'n');
    }, c);
  })));

module.exports = {};
