'use strict';
// 順序の一般的性質 (< は ⊊ として定義されているので, ℝ に限らずすべての集合で成り立つ)
const K = require('./kit');
const { X, prove } = K;

// ¬ x < x   … (R11)
prove('LtIrrefl', 'all x. ~ x < x', '[O1]', () => {
  const d = X.inst(X.defAx('lt'), ['x', 'x']);
  return X.gen(X.tc([], [d, X.refl('x')], '~ x < x'), 'x');
});

// x < y → y < z → x < z  … (R12)
prove('LtTrans', 'all x. all y. all z. (x < y -> y < z -> x < z)', '[O2]', () => {
  const body = X.assume([], 'x < y', (h1, c1) => X.assume(c1, 'y < z', (h2, c) => {
    const lxy = X.inst(X.defAx('lt'), ['x', 'y']), lyz = X.inst(X.defAx('lt'), ['y', 'z']), lxz = X.inst(X.defAx('lt'), ['x', 'z']);
    const sxy = X.inst(X.defAx('sub'), ['x', 'y']), syz = X.inst(X.defAx('sub'), ['y', 'z']), sxz = X.inst(X.defAx('sub'), ['x', 'z']), syx = X.inst(X.defAx('sub'), ['y', 'x']);
    // x ⊆ z
    const axy = X.tc(c, [h1, lxy, sxy], 'all u. (u in x -> u in y)');
    const ayz = X.tc(c, [h2, lyz, syz], 'all u. (u in y -> u in z)');
    const uxz = X.tc(c, [X.inst(axy, ['u']), X.inst(ayz, ['u'])], 'u in x -> u in z');
    const xsz = X.tc(c, [X.gen(uxz, 'u'), sxz], 'x sub z');
    // x ≠ z: x = z なら y ⊆ x となり, 外延性から x = y (x ≠ y に矛盾)
    const ne = X.assume(c, 'x = z', (e, c3) => {
      const ysz = X.tc(c3, [h2, lyz], 'y sub z');
      const ysx = X.rw(X.sym(e), ysz, 'y sub x');
      const ayx = X.tc(c3, [ysx, syx], 'all u. (u in y -> u in x)');
      const iff = X.tc(c3, [X.inst(axy, ['u']), X.inst(ayx, ['u'])], 'u in x <-> u in y');
      const ext = X.inst(X.axiom('Ext'), ['x', 'y']);
      return X.tc(c3, [X.gen(iff, 'u'), ext], 'x = y');
    });
    return X.tc(c, [ne, h1, lxy, xsz, lxz], 'x < z');
  }));
  return X.genAll(body, ['x', 'y', 'z']);
});

// x < y → y ≤ z → x < z
prove('LtLeTrans', 'all x. all y. all z. (x < y -> y <= z -> x < z)', '[O3]', () => {
  const body = X.assume([], 'x < y', (h1, c1) => X.assume(c1, 'y <= z', (h2, c) => {
    const t = X.inst(X.thm('LtTrans'), ['x', 'y', 'z']);
    const e = X.assume(c, 'y = z', (ey, c3) => X.rw(ey, X.hyp(c3, 0), 'x < z'));
    return X.tc(c, [h1, h2, t, e], 'x < z');
  }));
  return X.genAll(body, ['x', 'y', 'z']);
});

// x ≤ y → y < z → x < z
prove('LeLtTrans', 'all x. all y. all z. (x <= y -> y < z -> x < z)', '[O4]', () => {
  const body = X.assume([], 'x <= y', (h1, c1) => X.assume(c1, 'y < z', (h2, c) => {
    const t = X.inst(X.thm('LtTrans'), ['x', 'y', 'z']);
    const e = X.assume(c, 'x = y', (ex, c3) => X.rw(X.sym(ex), X.hyp(c3, 1), 'x < z'));
    return X.tc(c, [h1, h2, t, e], 'x < z');
  }));
  return X.genAll(body, ['x', 'y', 'z']);
});

// x ≤ y → y ≤ z → x ≤ z
prove('LeTrans', 'all x. all y. all z. (x <= y -> y <= z -> x <= z)', '[O5]', () => {
  const body = X.assume([], 'x <= y', (h1, c1) => X.assume(c1, 'y <= z', (h2, c) => {
    const t = X.inst(X.thm('LtLeTrans'), ['x', 'y', 'z']);
    const e = X.assume(c, 'x = y', (ex, c3) => X.rw(X.sym(ex), X.hyp(c3, 1), 'x <= z'));
    return X.tc(c, [h1, h2, t, e], 'x <= z');
  }));
  return X.genAll(body, ['x', 'y', 'z']);
});

// x ≤ y → y ≤ x → x = y
prove('LeAntisym', 'all x. all y. (x <= y -> y <= x -> x = y)', '[O6]', () => {
  const body = X.assume([], 'x <= y', (h1, c1) => X.assume(c1, 'y <= x', (h2, c) => {
    const t = X.inst(X.thm('LtTrans'), ['x', 'y', 'x']);
    const ir = X.inst(X.thm('LtIrrefl'), ['x']);
    const e = X.assume(c, 'y = x', (ey, c3) => X.sym(ey));
    return X.tc(c, [h1, h2, t, ir, e], 'x = y');
  }));
  return X.genAll(body, ['x', 'y']);
});

// x ≤ y → ¬ y < x
prove('LeNotLt', 'all x. all y. (x <= y -> ~ y < x)', '[O7]', () => {
  const body = X.assume([], 'x <= y', (h1, c) => {
    const t = X.inst(X.thm('LtTrans'), ['x', 'y', 'x']);
    const ir = X.inst(X.thm('LtIrrefl'), ['x']);
    const e = X.assume(c, 'x = y', (ex, c3) => X.assume(c3, 'y < x', (yx, c4) => {
      const xx = X.rw(X.sym(ex), yx, 'x < x');
      return X.tc(c4, [xx, ir], '~ y < x');
    }));
    return X.tc(c, [h1, t, ir, e], '~ y < x');
  });
  return X.genAll(body, ['x', 'y']);
});

// x, y ∈ ℝ → ¬ x < y → y ≤ x   (R13 を用いる)
prove('NotLtLe', 'all x. all y. (x in Real -> y in Real -> ~ x < y -> y <= x)', '[O8]', () => {
  const body = X.assume([], 'x in Real', (h1, c1) => X.assume(c1, 'y in Real', (h2, c2) => X.assume(c2, '~ x < y', (h3, c) => {
    const r13 = K.use('R13', ['x', 'y'], c);
    const e = X.assume(c, 'x = y', (ex, c4) => X.sym(ex));
    return X.tc(c, [h3, r13, e], 'y <= x');
  })));
  return X.genAll(body, ['x', 'y']);
});

module.exports = {};
