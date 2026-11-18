'use strict';
// 順序体の基本性質 (公理 (R1)–(R16) からの完全展開した証明)
const K = require('./kit');
const { X, prove, intro, use, calc, cases, mem } = K;
require('./p_order');

// ---------- 所属 ----------
prove('SubR', 'all x. all y. (x in Real -> y in Real -> x - y in Real)', '[F1]', () => intro(['x', 'y'], [], c => {
  const m = mem(c, 'x + -y');
  const d = X.inst(X.defAx('minus'), ['x', 'y']);
  return X.rw(X.sym(d), m, 'x - y in Real', c);
}));
prove('TwoR', '2 in Real', '[F2]', () => {
  const m = mem([], '1 + 1');
  return X.rw(X.sym(X.defAx('two')), m, '2 in Real', []);
});

// ---------- 加法 ----------
prove('AddCancel', 'all x. all y. all z. (x in Real -> y in Real -> z in Real -> x + z = y + z -> x = y)', '[F3]', () =>
  intro(['x', 'y', 'z'], ['x + z = y + z'], (c, [h]) => calc(c, 'x', [
    ['x + 0', use('R4', ['x'], c)],
    ['x + (z + -z)', use('R5', ['z'], c)],
    ['(x + z) + -z', use('R2', ['x', 'z', '-z'], c)],
    ['(y + z) + -z', h],
    ['y + (z + -z)', use('R2', ['y', 'z', '-z'], c)],
    ['y + 0', use('R5', ['z'], c)],
    ['y', use('R4', ['y'], c)],
  ])));

prove('NegUnique', 'all x. all y. (x in Real -> y in Real -> x + y = 0 -> y = -x)', '[F4]', () =>
  intro(['x', 'y'], ['x + y = 0'], (c, [h]) => calc(c, 'y', [
    ['y + 0', use('R4', ['y'], c)],
    ['y + (x + -x)', use('R5', ['x'], c)],
    ['(y + x) + -x', use('R2', ['y', 'x', '-x'], c)],
    ['(x + y) + -x', use('R3', ['y', 'x'], c)],
    ['0 + -x', h],
    ['-x + 0', use('R3', ['0', '-x'], c)],
    ['-x', use('R4', ['-x'], c)],
  ])));

prove('NegNeg', 'all x. (x in Real -> -(-x) = x)', '[F5]', () => intro(['x'], [], c => {
  const e = calc(c, '-x + x', [['x + -x', use('R3', ['-x', 'x'], c)], ['0', use('R5', ['x'], c)]]);
  const u = use('NegUnique', ['-x', 'x'], c, [e]);
  return X.sym(u);
}));

prove('NegZero', '-0 = 0', '[F6]', () => {
  const e = use('R4', ['0'], []);
  return X.sym(use('NegUnique', ['0', '0'], [], [e]));
});

prove('NegAdd', 'all x. all y. (x in Real -> y in Real -> -(x + y) = -x + -y)', '[F7]', () => intro(['x', 'y'], [], c => {
  const e = calc(c, '(x + y) + (-x + -y)', [
    ['x + (y + (-x + -y))', use('R2', ['x', 'y', '-x + -y'], c)],
    ['x + (y + (-y + -x))', use('R3', ['-x', '-y'], c)],
    ['x + ((y + -y) + -x)', use('R2', ['y', '-y', '-x'], c)],
    ['x + (0 + -x)', use('R5', ['y'], c)],
    ['x + (-x + 0)', use('R3', ['0', '-x'], c)],
    ['x + -x', use('R4', ['-x'], c)],
    ['0', use('R5', ['x'], c)],
  ]);
  return X.sym(use('NegUnique', ['x + y', '-x + -y'], c, [e]));
}));

// ---------- 乗法 ----------
prove('Mul0', 'all x. (x in Real -> x * 0 = 0)', '[F8]', () => intro(['x'], [], c => {
  const e = calc(c, 'x * 0 + x * 0', [
    ['x * (0 + 0)', use('R10', ['x', '0', '0'], c)],
    ['x * 0', use('R4', ['0'], c)],
    ['x * 0 + 0', use('R4', ['x * 0'], c)],
    ['0 + x * 0', use('R3', ['x * 0', '0'], c)],
  ]);
  return use('AddCancel', ['x * 0', '0', 'x * 0'], c, [e]);
}));

prove('NegMul', 'all x. all y. (x in Real -> y in Real -> (-x) * y = -(x * y))', '[F9]', () => intro(['x', 'y'], [], c => {
  const e = calc(c, 'x * y + (-x) * y', [
    ['y * x + (-x) * y', use('R7', ['x', 'y'], c)],
    ['y * x + y * (-x)', use('R7', ['-x', 'y'], c)],
    ['y * (x + -x)', use('R10', ['y', 'x', '-x'], c)],
    ['y * 0', use('R5', ['x'], c)],
    ['0', use('Mul0', ['y'], c)],
  ]);
  return use('NegUnique', ['x * y', '(-x) * y'], c, [e]);
}));

prove('MulNeg', 'all x. all y. (x in Real -> y in Real -> x * (-y) = -(x * y))', '[F10]', () => intro(['x', 'y'], [], c => calc(c, 'x * (-y)', [
  ['(-y) * x', use('R7', ['x', '-y'], c)],
  ['-(y * x)', use('NegMul', ['y', 'x'], c)],
  ['-(x * y)', use('R7', ['y', 'x'], c)],
])));

prove('NegNegMul', 'all x. all y. (x in Real -> y in Real -> (-x) * (-y) = x * y)', '[F11]', () => intro(['x', 'y'], [], c => calc(c, '(-x) * (-y)', [
  ['-(x * (-y))', use('NegMul', ['x', '-y'], c)],
  ['-(-(x * y))', use('MulNeg', ['x', 'y'], c)],
  ['x * y', use('NegNeg', ['x * y'], c)],
])));

// ---------- 減法 ----------
prove('SubAdd', 'all x. all y. (x in Real -> y in Real -> (x - y) + y = x)', '[F12]', () => intro(['x', 'y'], [], c => calc(c, '(x - y) + y', [
  ['(x + -y) + y', X.inst(X.defAx('minus'), ['x', 'y'])],
  ['x + (-y + y)', use('R2', ['x', '-y', 'y'], c)],
  ['x + (y + -y)', use('R3', ['-y', 'y'], c)],
  ['x + 0', use('R5', ['y'], c)],
  ['x', use('R4', ['x'], c)],
])));

prove('SubSelf', 'all x. (x in Real -> x - x = 0)', '[F13]', () => intro(['x'], [], c => calc(c, 'x - x', [
  ['x + -x', X.inst(X.defAx('minus'), ['x', 'x'])],
  ['0', use('R5', ['x'], c)],
])));

prove('SubNeg', 'all x. all y. (x in Real -> y in Real -> -(y - x) = x - y)', '[F14]', () => intro(['x', 'y'], [], c => calc(c, '-(y - x)', [
  ['-(y + -x)', X.inst(X.defAx('minus'), ['y', 'x'])],
  ['-y + -(-x)', use('NegAdd', ['y', '-x'], c)],
  ['-y + x', use('NegNeg', ['x'], c)],
  ['x + -y', use('R3', ['-y', 'x'], c)],
  ['x - y', X.inst(X.defAx('minus'), ['x', 'y'])],
])));

// (x + y) - (a + b) = (x - a) + (y - b)
prove('SubAddAdd', 'all x. all y. all a. all b. (x in Real -> y in Real -> a in Real -> b in Real -> (x + y) - (a + b) = (x - a) + (y - b))', '[F15]', () =>
  intro(['x', 'y', 'a', 'b'], [], c => {
    const lhs = calc(c, '(x + y) - (a + b)', [
      ['(x + y) + -(a + b)', X.inst(X.defAx('minus'), ['x + y', 'a + b'])],
      ['(x + y) + (-a + -b)', use('NegAdd', ['a', 'b'], c)],
      ['x + (y + (-a + -b))', use('R2', ['x', 'y', '-a + -b'], c)],
      ['x + ((y + -a) + -b)', use('R2', ['y', '-a', '-b'], c)],
      ['x + ((-a + y) + -b)', use('R3', ['y', '-a'], c)],
      ['x + (-a + (y + -b))', use('R2', ['-a', 'y', '-b'], c)],
      ['(x + -a) + (y + -b)', use('R2', ['x', '-a', 'y + -b'], c)],
      ['(x - a) + (y + -b)', X.inst(X.defAx('minus'), ['x', 'a'])],
      ['(x - a) + (y - b)', X.inst(X.defAx('minus'), ['y', 'b'])],
    ]);
    return lhs;
  }));

// a - b = (a - x) + (x - b)
prove('SubSplit', 'all a. all b. all x. (a in Real -> b in Real -> x in Real -> a - b = (a - x) + (x - b))', '[F16]', () =>
  intro(['a', 'b', 'x'], [], c => X.sym(calc(c, '(a - x) + (x - b)', [
    ['(a + -x) + (x - b)', X.inst(X.defAx('minus'), ['a', 'x'])],
    ['a + (-x + (x - b))', use('R2', ['a', '-x', 'x - b'], c)],
    ['a + ((x - b) + -x)', use('R3', ['-x', 'x - b'], c)],
    ['a + ((x + -b) + -x)', X.inst(X.defAx('minus'), ['x', 'b'])],
    ['a + (x + (-b + -x))', use('R2', ['x', '-b', '-x'], c)],
    ['a + (x + (-x + -b))', use('R3', ['-b', '-x'], c)],
    ['a + ((x + -x) + -b)', use('R2', ['x', '-x', '-b'], c)],
    ['a + (0 + -b)', use('R5', ['x'], c)],
    ['a + (-b + 0)', use('R3', ['0', '-b'], c)],
    ['a + -b', use('R4', ['-b'], c)],
    ['a - b', X.inst(X.defAx('minus'), ['a', 'b'])],
  ]))));

// c x - c a = c (x - a)
prove('MulSub', 'all c. all x. all a. (c in Real -> x in Real -> a in Real -> c * x - c * a = c * (x - a))', '[F17]', () =>
  intro(['c', 'x', 'a'], [], cx => X.sym(calc(cx, 'c * (x - a)', [
    ['c * (x + -a)', X.inst(X.defAx('minus'), ['x', 'a'])],
    ['c * x + c * (-a)', use('R10', ['c', 'x', '-a'], cx)],
    ['c * x + -(c * a)', use('MulNeg', ['c', 'a'], cx)],
    ['c * x - c * a', X.inst(X.defAx('minus'), ['c * x', 'c * a'])],
  ]))));

// x y - a b = x (y - b) + b (x - a)
prove('MulSubSplit', 'all x. all y. all a. all b. (x in Real -> y in Real -> a in Real -> b in Real -> x * y - a * b = x * (y - b) + b * (x - a))', '[F18]', () =>
  intro(['x', 'y', 'a', 'b'], [], c => {
    const r = calc(c, 'x * (y - b) + b * (x - a)', [
      ['(x * y - x * b) + b * (x - a)', use('MulSub', ['x', 'y', 'b'], c)],
      ['(x * y - x * b) + (b * x - b * a)', use('MulSub', ['b', 'x', 'a'], c)],
      ['(x * y - x * b) + (x * b - b * a)', use('R7', ['b', 'x'], c)],
      ['(x * y - x * b) + (x * b - a * b)', use('R7', ['b', 'a'], c)],
      ['x * y - a * b', X.sym(use('SubSplit', ['x * y', 'a * b', 'x * b'], c))],
    ]);
    return X.sym(r);
  }));

// ---------- 順序と加法 ----------
prove('LeAddRight', 'all x. all y. all z. (x in Real -> y in Real -> z in Real -> x <= y -> x + z <= y + z)', '[F19]', () =>
  intro(['x', 'y', 'z'], ['x <= y'], (c, [h]) => {
    const lt = use('R14', ['x', 'y', 'z'], c);
    const eq = X.assume(c, 'x = y', (e, c2) => K.cong(e, 'x + z', c2));
    return X.tc(c, [h, lt, eq], 'x + z <= y + z');
  }));

prove('AddLtLe', 'all x. all y. all u. all v. (x in Real -> y in Real -> u in Real -> v in Real -> x < y -> u <= v -> x + u < y + v)', '[F20]', () =>
  intro(['x', 'y', 'u', 'v'], ['x < y', 'u <= v'], (c, [h1, h2]) => {
    const a = use('R14', ['x', 'y', 'u'], c, [h1]);                  // x+u < y+u
    const b0 = use('LeAddRight', ['u', 'v', 'y'], c, [h2]);           // u+y ≤ v+y
    const b1 = X.rw(use('R3', ['u', 'y'], c), b0, 'y + u <= v + y', c);
    const b = X.rw(use('R3', ['v', 'y'], c), b1, 'y + u <= y + v', c);
    return use('LtLeTrans', ['x + u', 'y + u', 'y + v'], c, [a, b]);
  }));

prove('AddLeLe', 'all x. all y. all u. all v. (x in Real -> y in Real -> u in Real -> v in Real -> x <= y -> u <= v -> x + u <= y + v)', '[F21]', () =>
  intro(['x', 'y', 'u', 'v'], ['x <= y', 'u <= v'], (c, [h1, h2]) => {
    const a = use('LeAddRight', ['x', 'y', 'u'], c, [h1]);
    const b0 = use('LeAddRight', ['u', 'v', 'y'], c, [h2]);
    const b1 = X.rw(use('R3', ['u', 'y'], c), b0, 'y + u <= v + y', c);
    const b = X.rw(use('R3', ['v', 'y'], c), b1, 'y + u <= y + v', c);
    return use('LeTrans', ['x + u', 'y + u', 'y + v'], c, [a, b]);
  }));

prove('NegLt', 'all x. all y. (x in Real -> y in Real -> x < y -> -y < -x)', '[F22]', () =>
  intro(['x', 'y'], ['x < y'], (c, [h]) => {
    const a = use('R14', ['x', 'y', '-x + -y'], c, [h]);
    const l = calc(c, 'x + (-x + -y)', [
      ['(x + -x) + -y', use('R2', ['x', '-x', '-y'], c)], ['0 + -y', use('R5', ['x'], c)],
      ['-y + 0', use('R3', ['0', '-y'], c)], ['-y', use('R4', ['-y'], c)]]);
    const r = calc(c, 'y + (-x + -y)', [
      ['y + (-y + -x)', use('R3', ['-x', '-y'], c)], ['(y + -y) + -x', use('R2', ['y', '-y', '-x'], c)],
      ['0 + -x', use('R5', ['y'], c)], ['-x + 0', use('R3', ['0', '-x'], c)], ['-x', use('R4', ['-x'], c)]]);
    const a1 = X.rw(l, a, '-y < y + (-x + -y)', c);
    return X.rw(r, a1, '-y < -x', c);
  }));

prove('NegLe', 'all x. all y. (x in Real -> y in Real -> x <= y -> -y <= -x)', '[F23]', () =>
  intro(['x', 'y'], ['x <= y'], (c, [h]) => {
    const lt = use('NegLt', ['x', 'y'], c);
    const eq = X.assume(c, 'x = y', (e, c2) => X.sym(K.cong(e, '-x', c2)));
    return X.tc(c, [h, lt, eq], '-y <= -x');
  }));

prove('SubPos', 'all x. all y. (x in Real -> y in Real -> x < y -> 0 < y - x)', '[F24]', () =>
  intro(['x', 'y'], ['x < y'], (c, [h]) => {
    const a = use('R14', ['x', 'y', '-x'], c, [h]);
    const a1 = X.rw(use('R5', ['x'], c), a, '0 < y + -x', c);
    return X.rw(X.sym(X.inst(X.defAx('minus'), ['y', 'x'])), a1, '0 < y - x', c);
  }));

prove('PosSub', 'all x. all y. (x in Real -> y in Real -> 0 < y - x -> x < y)', '[F25]', () =>
  intro(['x', 'y'], ['0 < y - x'], (c, [h]) => {
    const a = use('R14', ['0', 'y - x', 'x'], c, [h]);
    const z = calc(c, '0 + x', [['x + 0', use('R3', ['0', 'x'], c)], ['x', use('R4', ['x'], c)]]);
    const a1 = X.rw(z, a, 'x < (y - x) + x', c);
    return X.rw(use('SubAdd', ['y', 'x'], c), a1, 'x < y', c);
  }));

prove('LtNe', 'all x. all y. (x < y -> x != y)', '[F26]', () => X.genAll(X.assume([], 'x < y', (h, c) => {
  const ir = X.inst(X.thm('LtIrrefl'), ['x']);
  const e = X.assume(c, 'x = y', (ex, c2) => X.rw(X.sym(ex), X.hyp(c2, 0), 'x < x', c2));
  return X.tc(c, [ir, e], 'x != y');
}), ['x', 'y']));

// ---------- 0 < 1, 2 ----------
prove('NegOneSq', '(-1) * (-1) = 1', '[F27]', () => {
  const c = [];
  return calc(c, '(-1) * (-1)', [['1 * 1', use('NegNegMul', ['1', '1'], c)], ['1', use('R8', ['1'], c)]]);
});
prove('ZeroLtOne', '0 < 1', '[F28]', () => {
  const c = [];
  const r13 = use('R13', ['0', '1'], c);
  const c3 = X.assume(c, '1 < 0', (h, c2) => {
    const a = use('NegLt', ['1', '0'], c2, [h]);                   // -0 < -1
    const a1 = X.rw(X.thm('NegZero'), a, '0 < -1', c2);
    const p = use('R15', ['-1', '-1'], c2, [a1, a1]);               // 0 < (-1)(-1)
    const p1 = X.rw(X.thm('NegOneSq'), p, '0 < 1', c2);
    return p1;
  });
  return X.tc(c, [r13, X.thm('R8b'), c3], '0 < 1');
});
prove('TwoPos', '0 < 2', '[F29]', () => {
  const c = [];
  const a = use('R14', ['0', '1', '1'], c, [X.thm('ZeroLtOne')]);   // 0+1 < 1+1
  const z = calc(c, '0 + 1', [['1 + 0', use('R3', ['0', '1'], c)], ['1', use('R4', ['1'], c)]]);
  const a1 = X.rw(z, a, '1 < 1 + 1', c);
  const a2 = X.rw(X.sym(X.defAx('two')), a1, '1 < 2', c);
  return use('LtTrans', ['0', '1', '2'], c, [X.thm('ZeroLtOne'), a2]);
});
prove('TwoNe', '2 != 0', '[F30]', () => X.neSym(use('LtNe', ['0', '2'], [], [X.thm('TwoPos')])));
prove('InvTwoR', '2^-1 in Real', '[F31]', () => use('R1_inv', ['2'], [], [X.thm('TwoNe')]));

// ---------- 乗法と順序 ----------
prove('MulLtPos', 'all x. all y. all z. (x in Real -> y in Real -> z in Real -> 0 < z -> x < y -> x * z < y * z)', '[F32]', () =>
  intro(['x', 'y', 'z'], ['0 < z', 'x < y'], (c, [hz, h]) => {
    const d = use('SubPos', ['x', 'y'], c, [h]);
    const p = use('R15', ['y - x', 'z'], c, [d, hz]);
    const e = calc(c, '(y - x) * z', [['z * (y - x)', use('R7', ['y - x', 'z'], c)], ['z * y - z * x', X.sym(use('MulSub', ['z', 'y', 'x'], c))],
      ['y * z - z * x', use('R7', ['z', 'y'], c)], ['y * z - x * z', use('R7', ['z', 'x'], c)]]);
    const p1 = X.rw(e, p, '0 < y * z - x * z', c);
    return use('PosSub', ['x * z', 'y * z'], c, [p1]);
  }));

prove('MulLeNonneg', 'all x. all y. all z. (x in Real -> y in Real -> z in Real -> 0 <= z -> x <= y -> x * z <= y * z)', '[F33]', () =>
  intro(['x', 'y', 'z'], ['0 <= z', 'x <= y'], (c, [hz, h]) => {
    const lt = use('MulLtPos', ['x', 'y', 'z'], c);
    const z0 = X.assume(c, '0 = z', (e, c2) => {
      const l = calc(c2, 'x * z', [['x * 0', X.sym(e)], ['0', use('Mul0', ['x'], c2)], ['y * 0', X.sym(use('Mul0', ['y'], c2))], ['y * z', e]]);
      return X.tc(c2, [l], 'x * z <= y * z');
    });
    const eq = X.assume(c, 'x = y', (e, c2) => X.tc(c2, [K.cong(e, 'x * z', c2)], 'x * z <= y * z'));
    return X.tc(c, [hz, h, lt, z0, eq], 'x * z <= y * z');
  }));

prove('InvPos', 'all x. (x in Real -> 0 < x -> 0 < x^-1)', '[F34]', () =>
  intro(['x'], ['0 < x'], (c, [h]) => {
    const nz = X.neSym(use('LtNe', ['0', 'x'], c, [h]));          // x ≠ 0
    const f = [nz];
    const one = use('R9', ['x'], c, f);                              // x x^{-1} = 1
    const r13 = use('R13', ['0', 'x^-1'], c, f);
    const zero = X.assume(c, '0 = x^-1', (e, c2) => {               // 0 = x^{-1} なら 1 = 0
      const l = calc(c2, '1', [['x * x^-1', X.sym(one)], ['x * 0', X.sym(e)], ['0', use('Mul0', ['x'], c2)]]);
      return X.tc(c2, [X.sym(l), X.thm('R8b')], '0 < x^-1');
    });
    const neg = X.assume(c, 'x^-1 < 0', (hn, c2) => {
      const a = X.rw(X.thm('NegZero'), use('NegLt', ['x^-1', '0'], c2, [hn, ...f]), '0 < -(x^-1)', c2);
      const p = use('R15', ['x', '-(x^-1)'], c2, [h, a, ...f]);
      const e = calc(c2, 'x * -(x^-1)', [['-(x * x^-1)', use('MulNeg', ['x', 'x^-1'], c2, f)], ['-1', one]]);
      const p1 = X.rw(e, p, '0 < -1', c2);
      const m1 = X.rw(X.thm('NegZero'), use('NegLt', ['0', '1'], c2, [X.thm('ZeroLtOne')]), '-1 < 0', c2);
      const z = use('LtTrans', ['0', '-1', '0'], c2, [p1, m1]);
      return X.tc(c2, [z, X.inst(X.thm('LtIrrefl'), ['0'])], '0 < x^-1');
    });
    return X.tc(c, [r13, zero, neg], '0 < x^-1');
  }));

// ---------- ε/2 ----------
prove('HalfPos', 'all e. (e in Real -> 0 < e -> 0 < e * 2^-1)', '[F35]', () =>
  intro(['e'], ['0 < e'], (c, [h]) => {
    const ip = use('InvPos', ['2'], c, [X.thm('TwoPos')]);
    return use('R15', ['e', '2^-1'], c, [h, ip]);
  }));
prove('HalfSum', 'all e. (e in Real -> e * 2^-1 + e * 2^-1 = e)', '[F36]', () =>
  intro(['e'], [], c => calc(c, 'e * 2^-1 + e * 2^-1', [
    ['(e * 2^-1) * 1 + e * 2^-1', use('R8', ['e * 2^-1'], c)],
    ['(e * 2^-1) * 1 + (e * 2^-1) * 1', use('R8', ['e * 2^-1'], c)],
    ['(e * 2^-1) * (1 + 1)', use('R10', ['e * 2^-1', '1', '1'], c)],
    ['(e * 2^-1) * 2', X.defAx('two')],
    ['e * (2^-1 * 2)', use('R6', ['e', '2^-1', '2'], c)],
    ['e * (2 * 2^-1)', use('R7', ['2^-1', '2'], c)],
    ['e * 1', use('R9', ['2'], c, [X.thm('TwoNe')])],
    ['e', use('R8', ['e'], c)],
  ])));

module.exports = {};
