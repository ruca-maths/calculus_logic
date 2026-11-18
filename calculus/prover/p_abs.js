'use strict';
// 絶対値 (テキスト第1章 1.1節)
const K = require('./kit');
const { X, prove, intro, use, calc, cases, mem } = K;
require('./p_nat');

const dabs = x => X.inst(X.defAx('abs'), [x]);

prove('AbsOfNonneg', 'all x. (0 <= x -> abs(x) = x)', '[A1]', () =>
  X.gen(X.assume([], '0 <= x', (h, c) => X.tc(c, [h, dabs('x')], 'abs(x) = x')), 'x'));

prove('NotLeLt', 'all x. all y. (x in Real -> y in Real -> ~ y <= x -> x < y)', '[A2]', () =>
  intro(['x', 'y'], ['~ y <= x'], (c, [h]) => X.tc(c, [h, use('NotLtLe', ['x', 'y'], c)], 'x < y')));

prove('AbsOfNeg', 'all x. (x < 0 -> abs(x) = -x)', '[A3]', () =>
  X.gen(X.assume([], 'x < 0', (h, c) => X.tc(c, [h, dabs('x'), X.inst(X.thm('LeNotLt'), ['0', 'x'])], 'abs(x) = -x')), 'x'));

prove('AbsNonpos', 'all x. (x in Real -> x <= 0 -> abs(x) = -x)', '[A4]', () =>
  intro(['x'], ['x <= 0'], (c, [h]) => {
    const lt = X.inst(X.thm('AbsOfNeg'), ['x']);
    const eq = X.assume(c, 'x = 0', (e, c2) => {
      const z = use('AbsOfNonneg', ['x'], c2, [X.tc(c2, [X.sym(e)], '0 <= x')]);
      const nz = calc(c2, 'x', [['0', e], ['-0', X.sym(X.thm('NegZero'))], ['-x', X.sym(e)]]);
      return X.trans(z, nz, c2);
    });
    return X.tc(c, [h, lt, eq], 'abs(x) = -x');
  }));

prove('AbsR', 'all x. (x in Real -> abs(x) in Real)', '[A5]', () =>
  intro(['x'], [], c => {
    const d = dabs('x');
    const a = X.assume(c, '0 <= x & abs(x) = x', (h, c2) => X.rw(X.sym(X.tc(c2, [h], 'abs(x) = x')), X.hyp(c2, 0), 'abs(x) in Real', c2));
    const b = X.assume(c, '~ 0 <= x & abs(x) = -x', (h, c2) => X.rw(X.sym(X.tc(c2, [h], 'abs(x) = -x')), mem(c2, '-x'), 'abs(x) in Real', c2));
    return X.tc(c, [d, a, b], 'abs(x) in Real');
  }));

prove('AbsNonneg', 'all x. (x in Real -> 0 <= abs(x))', '[A6]', () =>
  intro(['x'], [], c => {
    const pos = X.assume(c, '0 <= x', (h, c2) => X.rw(X.sym(use('AbsOfNonneg', ['x'], c2, [h])), h, '0 <= abs(x)', c2));
    const neg = X.assume(c, '~ 0 <= x', (h, c2) => {
      const lt = use('NotLeLt', ['x', '0'], c2, [h]);
      const a = X.rw(X.thm('NegZero'), use('NegLt', ['x', '0'], c2, [lt]), '0 < -x', c2);
      const e = use('AbsOfNeg', ['x'], c2, [lt]);
      return X.tc(c2, [X.rw(X.sym(e), a, '0 < abs(x)', c2)], '0 <= abs(x)');
    });
    return X.tc(c, [pos, neg], '0 <= abs(x)');
  }));

prove('AbsNeg', 'all x. (x in Real -> abs(-x) = abs(x))', '[A7]', () =>
  intro(['x'], [], c => {
    const r = use('R13', ['x', '0'], c);
    const c1 = h => (hh, c2) => null;
    const neg = X.assume(c, 'x < 0', (h, c2) => {
      const p = X.rw(X.thm('NegZero'), use('NegLt', ['x', '0'], c2, [h]), '0 < -x', c2);
      const a = use('AbsOfNonneg', ['-x'], c2, [X.tc(c2, [p], '0 <= -x')]);
      return X.trans(a, X.sym(use('AbsOfNeg', ['x'], c2, [h])), c2);
    });
    const zero = X.assume(c, 'x = 0', (h, c2) => {
      const nx = calc(c2, '-x', [['-0', h], ['0', X.thm('NegZero')], ['x', X.sym(h)]]);
      return K.cong(nx, 'abs(-x)', c2);
    });
    const pos = X.assume(c, '0 < x', (h, c2) => {
      const n = X.rw(X.thm('NegZero'), use('NegLt', ['0', 'x'], c2, [h]), '-x < 0', c2);
      const a = use('AbsOfNeg', ['-x'], c2, [n]);
      const b = use('AbsOfNonneg', ['x'], c2, [X.tc(c2, [h], '0 <= x')]);
      return calc(c2, 'abs(-x)', [['-(-x)', a], ['x', use('NegNeg', ['x'], c2)], ['abs(x)', X.sym(b)]]);
    });
    return X.tc(c, [r, neg, zero, pos], 'abs(-x) = abs(x)');
  }));

prove('AbsBound', 'all x. (x in Real -> -abs(x) <= x & x <= abs(x))', '[A8]', () =>
  intro(['x'], [], c => {
    const pos = X.assume(c, '0 <= x', (h, c2) => {
      const e = use('AbsOfNonneg', ['x'], c2, [h]);
      const nx = X.rw(X.thm('NegZero'), use('NegLe', ['0', 'x'], c2, [h]), '-x <= 0', c2);
      const a = use('LeTrans', ['-x', '0', 'x'], c2, [nx, h]);               // -x ≤ x
      const a1 = X.rw(X.sym(e), a, '-abs(x) <= x', c2);
      const b = X.rw(X.sym(e), X.tc(c2, [X.refl('x')], 'x <= x'), 'x <= abs(x)', c2);
      return X.tc(c2, [a1, b], '-abs(x) <= x & x <= abs(x)');
    });
    const neg = X.assume(c, '~ 0 <= x', (h, c2) => {
      const lt = use('NotLeLt', ['x', '0'], c2, [h]);
      const e = use('AbsOfNeg', ['x'], c2, [lt]);                            // |x| = -x
      const ne = calc(c2, '-abs(x)', [['-(-x)', e], ['x', use('NegNeg', ['x'], c2)]]);
      const a = X.tc(c2, [ne], '-abs(x) <= x');
      const p = X.rw(X.thm('NegZero'), use('NegLt', ['x', '0'], c2, [lt]), '0 < -x', c2);
      const b0 = use('LtTrans', ['x', '0', '-x'], c2, [lt, p]);
      const b = X.rw(X.sym(e), X.tc(c2, [b0], 'x <= -x'), 'x <= abs(x)', c2);
      return X.tc(c2, [a, b], '-abs(x) <= x & x <= abs(x)');
    });
    return X.tc(c, [pos, neg], '-abs(x) <= x & x <= abs(x)');
  }));

prove('AbsLe', 'all x. all y. (x in Real -> y in Real -> abs(x) <= y -> -y <= x & x <= y)', '[A9]', () =>
  intro(['x', 'y'], ['abs(x) <= y'], (c, [h]) => {
    const bd = use('AbsBound', ['x'], c);
    const r = use('LeTrans', ['x', 'abs(x)', 'y'], c, [X.tc(c, [bd], 'x <= abs(x)'), h]);
    const n = use('NegLe', ['abs(x)', 'y'], c, [h]);
    const l = use('LeTrans', ['-y', '-abs(x)', 'x'], c, [n, X.tc(c, [bd], '-abs(x) <= x')]);
    return X.tc(c, [l, r], '-y <= x & x <= y');
  }));

prove('LeAbs', 'all x. all y. (x in Real -> y in Real -> -y <= x -> x <= y -> abs(x) <= y)', '[A10]', () =>
  intro(['x', 'y'], ['-y <= x', 'x <= y'], (c, [h1, h2]) => {
    const pos = X.assume(c, '0 <= x', (h, c2) => X.rw(X.sym(use('AbsOfNonneg', ['x'], c2, [h])), h2, 'abs(x) <= y', c2));
    const neg = X.assume(c, '~ 0 <= x', (h, c2) => {
      const lt = use('NotLeLt', ['x', '0'], c2, [h]);
      const e = use('AbsOfNeg', ['x'], c2, [lt]);
      const a = X.rw(use('NegNeg', ['y'], c2), use('NegLe', ['-y', 'x'], c2, [h1]), '-x <= y', c2);
      return X.rw(X.sym(e), a, 'abs(x) <= y', c2);
    });
    return X.tc(c, [pos, neg], 'abs(x) <= y');
  }));

prove('AbsLt', 'all x. all y. (x in Real -> y in Real -> abs(x) < y -> -y < x & x < y)', '[A11]', () =>
  intro(['x', 'y'], ['abs(x) < y'], (c, [h]) => {
    const bd = use('AbsBound', ['x'], c);
    const r = use('LeLtTrans', ['x', 'abs(x)', 'y'], c, [X.tc(c, [bd], 'x <= abs(x)'), h]);
    const n = use('NegLt', ['abs(x)', 'y'], c, [h]);
    const l = use('LtLeTrans', ['-y', '-abs(x)', 'x'], c, [n, X.tc(c, [bd], '-abs(x) <= x')]);
    return X.tc(c, [l, r], '-y < x & x < y');
  }));

prove('LtAbs', 'all x. all y. (x in Real -> y in Real -> -y < x -> x < y -> abs(x) < y)', '[A12]', () =>
  intro(['x', 'y'], ['-y < x', 'x < y'], (c, [h1, h2]) => {
    const pos = X.assume(c, '0 <= x', (h, c2) => X.rw(X.sym(use('AbsOfNonneg', ['x'], c2, [h])), h2, 'abs(x) < y', c2));
    const neg = X.assume(c, '~ 0 <= x', (h, c2) => {
      const lt = use('NotLeLt', ['x', '0'], c2, [h]);
      const e = use('AbsOfNeg', ['x'], c2, [lt]);
      const a = X.rw(use('NegNeg', ['y'], c2), use('NegLt', ['-y', 'x'], c2, [h1]), '-x < y', c2);
      return X.rw(X.sym(e), a, 'abs(x) < y', c2);
    });
    return X.tc(c, [pos, neg], 'abs(x) < y');
  }));

prove('AbsSubComm', 'all x. all y. (x in Real -> y in Real -> abs(x - y) = abs(y - x))', '[A13]', () =>
  intro(['x', 'y'], [], c => {
    const a = use('AbsNeg', ['y - x'], c);                 // |-(y-x)| = |y-x|
    return X.rw(use('SubNeg', ['x', 'y'], c), a, 'abs(x - y) = abs(y - x)', c);
  }));

// 三角不等式 (テキスト命題1.2)
prove('Triangle', 'all a. all b. (a in Real -> b in Real -> abs(a + b) <= abs(a) + abs(b))', '命題1.2', () =>
  intro(['a', 'b'], [], c => {
    const ba = use('AbsBound', ['a'], c), bb = use('AbsBound', ['b'], c);
    const lo = use('AddLeLe', ['-abs(a)', 'a', '-abs(b)', 'b'], c, [X.tc(c, [ba], '-abs(a) <= a'), X.tc(c, [bb], '-abs(b) <= b')]);
    const lo1 = X.rw(X.sym(use('NegAdd', ['abs(a)', 'abs(b)'], c)), lo, '-(abs(a) + abs(b)) <= a + b', c);
    const hi = use('AddLeLe', ['a', 'abs(a)', 'b', 'abs(b)'], c, [X.tc(c, [ba], 'a <= abs(a)'), X.tc(c, [bb], 'b <= abs(b)')]);
    return use('LeAbs', ['a + b', 'abs(a) + abs(b)'], c, [lo1, hi]);
  }));

prove('AbsPos', 'all x. (x in Real -> x != 0 -> 0 < abs(x))', '[A14]', () =>
  intro(['x'], ['x != 0'], (c, [h]) => {
    const r = use('R13', ['x', '0'], c);
    const neg = X.assume(c, 'x < 0', (hn, c2) => {
      const p = X.rw(X.thm('NegZero'), use('NegLt', ['x', '0'], c2, [hn]), '0 < -x', c2);
      return X.rw(X.sym(use('AbsOfNeg', ['x'], c2, [hn])), p, '0 < abs(x)', c2);
    });
    const pos = X.assume(c, '0 < x', (hp, c2) => X.rw(X.sym(use('AbsOfNonneg', ['x'], c2, [X.tc(c2, [hp], '0 <= x')])), hp, '0 < abs(x)', c2));
    return X.tc(c, [r, h, neg, pos], '0 < abs(x)');
  }));

prove('SubNeZero', 'all x. all y. (x in Real -> y in Real -> x != y -> x - y != 0)', '[A15]', () =>
  intro(['x', 'y'], ['x != y'], (c, [h]) => {
    const e = X.assume(c, 'x - y = 0', (z, c2) => {
      const l = calc(c2, 'x', [['(x - y) + y', X.sym(use('SubAdd', ['x', 'y'], c2))], ['0 + y', z], ['y + 0', use('R3', ['0', 'y'], c2)], ['y', use('R4', ['y'], c2)]]);
      return l;
    });
    return X.tc(c, [h, e], 'x - y != 0');
  }));

prove('MulNonneg', 'all x. all y. (x in Real -> y in Real -> 0 <= x -> 0 <= y -> 0 <= x * y)', '[A16]', () =>
  intro(['x', 'y'], ['0 <= x', '0 <= y'], (c, [hx, hy]) => {
    const a = use('MulLeNonneg', ['0', 'x', 'y'], c, [hy, hx]);           // 0·y ≤ x·y
    const z = calc(c, '0 * y', [['y * 0', use('R7', ['0', 'y'], c)], ['0', use('Mul0', ['y'], c)]]);
    return X.rw(z, a, '0 <= x * y', c);
  }));

prove('AbsMul', 'all x. all y. (x in Real -> y in Real -> abs(x * y) = abs(x) * abs(y))', '[A17]', () =>
  intro(['x', 'y'], [], c => {
    const sx = X.assume, res = 'abs(x * y) = abs(x) * abs(y)';
    const caseXY = (px, py) => null;
    const mk = (hx, hy) => X.assume(c, hx, (h1, c1) => X.assume(c1, hy, (h2, c2) => {
      const xNon = hx === '0 <= x', yNon = hy === '0 <= y';
      const ex = xNon ? use('AbsOfNonneg', ['x'], c2, [h1]) : use('AbsOfNeg', ['x'], c2, [use('NotLeLt', ['x', '0'], c2, [h1])]);
      const ey = yNon ? use('AbsOfNonneg', ['y'], c2, [h2]) : use('AbsOfNeg', ['y'], c2, [use('NotLeLt', ['y', '0'], c2, [h2])]);
      const rhs0 = calc(c2, 'abs(x) * abs(y)', [[(xNon ? 'x' : '-x') + ' * abs(y)', ex], [(xNon ? 'x' : '-x') + ' * ' + (yNon ? 'y' : '-y'), ey]]);
      let lhs;
      if (xNon && yNon) {
        lhs = calc(c2, 'abs(x * y)', [['x * y', use('AbsOfNonneg', ['x * y'], c2, [use('MulNonneg', ['x', 'y'], c2, [h1, h2])])]]);
      } else if (!xNon && !yNon) {
        const nx = X.tc(c2, [X.rw(X.thm('NegZero'), use('NegLt', ['x', '0'], c2, [use('NotLeLt', ['x', '0'], c2, [h1])]), '0 < -x', c2)], '0 <= -x');
        const ny = X.tc(c2, [X.rw(X.thm('NegZero'), use('NegLt', ['y', '0'], c2, [use('NotLeLt', ['y', '0'], c2, [h2])]), '0 < -y', c2)], '0 <= -y');
        const p = X.rw(use('NegNegMul', ['x', 'y'], c2), use('MulNonneg', ['-x', '-y'], c2, [nx, ny]), '0 <= x * y', c2);
        lhs = calc(c2, 'abs(x * y)', [['x * y', use('AbsOfNonneg', ['x * y'], c2, [p])], ['(-x) * (-y)', X.sym(use('NegNegMul', ['x', 'y'], c2))]]);
      } else if (xNon) { // 0 ≤ x, y < 0
        const ny = X.tc(c2, [X.rw(X.thm('NegZero'), use('NegLt', ['y', '0'], c2, [use('NotLeLt', ['y', '0'], c2, [h2])]), '0 < -y', c2)], '0 <= -y');
        const p = X.rw(use('MulNeg', ['x', 'y'], c2), use('MulNonneg', ['x', '-y'], c2, [h1, ny]), '0 <= -(x * y)', c2);
        const q = X.rw(use('NegNeg', ['x * y'], c2), use('NegLe', ['0', '-(x * y)'], c2, [p]), 'x * y <= -0', c2);
        const q1 = X.rw(X.thm('NegZero'), q, 'x * y <= 0', c2);
        lhs = calc(c2, 'abs(x * y)', [['-(x * y)', use('AbsNonpos', ['x * y'], c2, [q1])], ['x * (-y)', X.sym(use('MulNeg', ['x', 'y'], c2))]]);
      } else { // x < 0, 0 ≤ y
        const nx = X.tc(c2, [X.rw(X.thm('NegZero'), use('NegLt', ['x', '0'], c2, [use('NotLeLt', ['x', '0'], c2, [h1])]), '0 < -x', c2)], '0 <= -x');
        const p = X.rw(use('NegMul', ['x', 'y'], c2), use('MulNonneg', ['-x', 'y'], c2, [nx, h2]), '0 <= -(x * y)', c2);
        const q = X.rw(use('NegNeg', ['x * y'], c2), use('NegLe', ['0', '-(x * y)'], c2, [p]), 'x * y <= -0', c2);
        const q1 = X.rw(X.thm('NegZero'), q, 'x * y <= 0', c2);
        lhs = calc(c2, 'abs(x * y)', [['-(x * y)', use('AbsNonpos', ['x * y'], c2, [q1])], ['(-x) * y', X.sym(use('NegMul', ['x', 'y'], c2))]]);
      }
      return X.trans(lhs, X.sym(rhs0), c2);
    }));
    const l1 = mk('0 <= x', '0 <= y'), l2 = mk('0 <= x', '~ 0 <= y'), l3 = mk('~ 0 <= x', '0 <= y'), l4 = mk('~ 0 <= x', '~ 0 <= y');
    return X.tc(c, [l1, l2, l3, l4], res);
  }));

module.exports = {};
