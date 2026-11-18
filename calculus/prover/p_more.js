'use strict';
// 順序体の補題(追加): 逆数, 不等式の操作
const K = require('./kit');
const { X, prove, intro, use, calc, mem } = K;
require('./p_ch4');

const R = (...xs) => xs; // 可読性のため

// ---- 加法と順序 ----
prove('LeAddNonneg', 'all x. all y. (x in Real -> y in Real -> 0 <= y -> x <= x + y)', '[E1]', () => intro(['x', 'y'], ['0 <= y'], (c, [h]) => {
  const l = use('LeAddRight', ['0', 'y', 'x'], c, [h]);
  const l1 = X.rw(calc(c, '0 + x', [['x + 0', use('R3', ['0', 'x'], c)], ['x', use('R4', ['x'], c)]]), l, 'x <= y + x', c);
  return X.rw(use('R3', ['y', 'x'], c), l1, 'x <= x + y', c);
}));
prove('LeAddNonnegL', 'all x. all y. (x in Real -> y in Real -> 0 <= y -> x <= y + x)', '[E2]', () => intro(['x', 'y'], ['0 <= y'], (c, [h]) =>
  X.rw(use('R3', ['x', 'y'], c), use('LeAddNonneg', ['x', 'y'], c, [h]), 'x <= y + x', c)));
prove('LtAddPos', 'all x. all y. (x in Real -> y in Real -> 0 < y -> x < x + y)', '[E3]', () => intro(['x', 'y'], ['0 < y'], (c, [h]) => {
  const l = use('R14', ['0', 'y', 'x'], c, [h]);
  const l1 = X.rw(calc(c, '0 + x', [['x + 0', use('R3', ['0', 'x'], c)], ['x', use('R4', ['x'], c)]]), l, 'x < y + x', c);
  return X.rw(use('R3', ['y', 'x'], c), l1, 'x < x + y', c);
}));
prove('LtAddCancel', 'all x. all y. all z. (x in Real -> y in Real -> z in Real -> x + z < y + z -> x < y)', '[E4]', () => intro(['x', 'y', 'z'], ['x + z < y + z'], (c, [h]) => {
  const l = use('R14', ['x + z', 'y + z', '-z'], c, [h]);
  const s = t => calc(c, `(${t} + z) + -z`, [[`${t} + (z + -z)`, use('R2', [t, 'z', '-z'], c)], [`${t} + 0`, use('R5', ['z'], c)], [t, use('R4', [t], c)]]);
  return X.rw(s('y'), X.rw(s('x'), l, 'x < (y + z) + -z', c), 'x < y', c);
}));
prove('AddPosPos', 'all x. all y. (x in Real -> y in Real -> 0 < x -> 0 < y -> 0 < x + y)', '[E5]', () => intro(['x', 'y'], ['0 < x', '0 < y'], (c, [hx, hy]) =>
  use('LtTrans', ['0', 'x', 'x + y'], c, [hx, use('LtAddPos', ['x', 'y'], c, [hy])])));
prove('AddNonnegNonneg', 'all x. all y. (x in Real -> y in Real -> 0 <= x -> 0 <= y -> 0 <= x + y)', '[E6]', () => intro(['x', 'y'], ['0 <= x', '0 <= y'], (c, [hx, hy]) =>
  use('LeTrans', ['0', 'x', 'x + y'], c, [hx, use('LeAddNonneg', ['x', 'y'], c, [hy])])));
prove('AddLtLt', 'all x. all y. all u. all v. (x in Real -> y in Real -> u in Real -> v in Real -> x < y -> u < v -> x + u < y + v)', '[E7]', () =>
  intro(['x', 'y', 'u', 'v'], ['x < y', 'u < v'], (c, [h1, h2]) => use('AddLtLe', ['x', 'y', 'u', 'v'], c, [h1, X.tc(c, [h2], 'u <= v')])));

// ---- 乗法と順序 ----
prove('MulLtPosL', 'all x. all y. all z. (x in Real -> y in Real -> z in Real -> 0 < z -> x < y -> z * x < z * y)', '[E8]', () => intro(['x', 'y', 'z'], ['0 < z', 'x < y'], (c, [hz, h]) => {
  const l = use('MulLtPos', ['x', 'y', 'z'], c, [hz, h]);
  return X.rw(use('R7', ['y', 'z'], c), X.rw(use('R7', ['x', 'z'], c), l, 'z * x < y * z', c), 'z * x < z * y', c);
}));
prove('MulLeNonnegL', 'all x. all y. all z. (x in Real -> y in Real -> z in Real -> 0 <= z -> x <= y -> z * x <= z * y)', '[E9]', () => intro(['x', 'y', 'z'], ['0 <= z', 'x <= y'], (c, [hz, h]) => {
  const l = use('MulLeNonneg', ['x', 'y', 'z'], c, [hz, h]);
  return X.rw(use('R7', ['y', 'z'], c), X.rw(use('R7', ['x', 'z'], c), l, 'z * x <= y * z', c), 'z * x <= z * y', c);
}));
prove('PosNonneg', 'all x. (0 < x -> 0 <= x)', '[E10]', () => X.gen(X.assume([], '0 < x', (h, c) => X.tc(c, [h], '0 <= x')), 'x'));
prove('MulPosPos', 'all x. all y. (x in Real -> y in Real -> 0 < x -> 0 < y -> 0 < x * y)', '[E11]', () => intro(['x', 'y'], ['0 < x', '0 < y'], (c, [a, b]) => use('R15', ['x', 'y'], c, [a, b])));
// 0 ≤ x ≤ y, 0 ≤ u ≤ v → x u ≤ y v
prove('MulLeLe', 'all x. all y. all u. all v. (x in Real -> y in Real -> u in Real -> v in Real -> 0 <= x -> 0 <= u -> x <= y -> u <= v -> x * u <= y * v)', '[E12]', () =>
  intro(['x', 'y', 'u', 'v'], ['0 <= x', '0 <= u', 'x <= y', 'u <= v'], (c, [hx, hu, hxy, huv]) => {
    const yn = use('LeTrans', ['0', 'x', 'y'], c, [hx, hxy]);
    const a = use('MulLeNonneg', ['x', 'y', 'u'], c, [hu, hxy]);
    const b = use('MulLeNonnegL', ['u', 'v', 'y'], c, [yn, huv]);
    return use('LeTrans', ['x * u', 'y * u', 'y * v'], c, [a, b]);
  }));

// ---- 逆数 ----
prove('InvUnique', 'all x. all y. (x in Real -> y in Real -> x != 0 -> x * y = 1 -> y = x^-1)', '[E13]', () => intro(['x', 'y'], ['x != 0', 'x * y = 1'], (c, [hz, h]) =>
  calc(c, 'y', [['y * 1', X.sym(use('R8', ['y'], c))], ['y * (x * x^-1)', X.sym(use('R9', ['x'], c, [hz]))], ['(y * x) * x^-1', X.sym(use('R6', ['y', 'x', 'x^-1'], c, [hz]))],
    ['(x * y) * x^-1', use('R7', ['y', 'x'], c)], ['1 * x^-1', h], ['x^-1 * 1', use('R7', ['1', 'x^-1'], c, [hz])], ['x^-1', use('R8', ['x^-1'], c, [hz])]])));
prove('InvNe0', 'all x. (x in Real -> x != 0 -> x^-1 != 0)', '[E14]', () => intro(['x'], ['x != 0'], (c, [hz]) => X.raa(c, 'x^-1 != 0', (hn, c2) => {
  const e = X.tc(c2, [hn], 'x^-1 = 0');
  const one = calc(c2, '1', [['x * x^-1', X.sym(use('R9', ['x'], c2, [hz]))], ['x * 0', e], ['0', use('Mul0', ['x'], c2)]]);
  return [one, X.neSym(X.thm('R8b'))];
})));
prove('MulNe0', 'all x. all y. (x in Real -> y in Real -> x != 0 -> y != 0 -> x * y != 0)', '[E15]', () => intro(['x', 'y'], ['x != 0', 'y != 0'], (c, [hx, hy]) => X.raa(c, 'x * y != 0', (hn, c2) => {
  const e = X.tc(c2, [hn], 'x * y = 0');
  const yy = calc(c2, 'y', [['1 * y', X.sym(calc(c2, '1 * y', [['y * 1', use('R7', ['1', 'y'], c2)], ['y', use('R8', ['y'], c2)]]))],
    ['(x^-1 * x) * y', X.sym(calc(c2, 'x^-1 * x', [['x * x^-1', use('R7', ['x^-1', 'x'], c2, [hx])], ['1', use('R9', ['x'], c2, [hx])]]))],
    ['x^-1 * (x * y)', use('R6', ['x^-1', 'x', 'y'], c2, [hx])], ['x^-1 * 0', e], ['0', use('Mul0', ['x^-1'], c2, [hx])]]);
  return [yy, hy];
})));
prove('InvMul', 'all x. all y. (x in Real -> y in Real -> x != 0 -> y != 0 -> (x * y)^-1 = x^-1 * y^-1)', '[E16]', () => intro(['x', 'y'], ['x != 0', 'y != 0'], (c, [hx, hy]) => {
  const f = [hx, hy];
  const p = calc(c, '(x * y) * (x^-1 * y^-1)', [
    ['x * (y * (x^-1 * y^-1))', use('R6', ['x', 'y', 'x^-1 * y^-1'], c, f)],
    ['x * (y * (y^-1 * x^-1))', use('R7', ['x^-1', 'y^-1'], c, f)],
    ['x * ((y * y^-1) * x^-1)', X.sym(use('R6', ['y', 'y^-1', 'x^-1'], c, f))],
    ['x * (1 * x^-1)', use('R9', ['y'], c, f)],
    ['x * (x^-1 * 1)', use('R7', ['1', 'x^-1'], c, f)],
    ['x * x^-1', use('R8', ['x^-1'], c, f)],
    ['1', use('R9', ['x'], c, f)]]);
  const nz = use('MulNe0', ['x', 'y'], c, f);
  return X.sym(use('InvUnique', ['x * y', 'x^-1 * y^-1'], c, [...f, nz, p]));
}));
prove('Abs1', 'abs(1) = 1', '[E17]', () => use('AbsOfNonneg', ['1'], [], [X.tc([], [X.thm('ZeroLtOne')], '0 <= 1')]));
prove('AbsInv', 'all x. (x in Real -> x != 0 -> abs(x^-1) = abs(x)^-1)', '[E18]', () => intro(['x'], ['x != 0'], (c, [hx]) => {
  const p = calc(c, 'abs(x) * abs(x^-1)', [['abs(x * x^-1)', X.sym(use('AbsMul', ['x', 'x^-1'], c, [hx]))], ['abs(1)', use('R9', ['x'], c, [hx])], ['1', X.thm('Abs1')]]);
  const nz = X.neSym(use('LtNe', ['0', 'abs(x)'], c, [use('AbsPos', ['x'], c, [hx])]));
  return use('InvUnique', ['abs(x)', 'abs(x^-1)'], c, [hx, nz, p]);
}));
// 0 < x < y → y^{-1} < x^{-1}
prove('InvLt', 'all x. all y. (x in Real -> y in Real -> 0 < x -> x < y -> y^-1 < x^-1)', '[E19]', () => intro(['x', 'y'], ['0 < x', 'x < y'], (c, [hx, h]) => {
  const hy = use('LtTrans', ['0', 'x', 'y'], c, [hx, h]);
  const nx = X.neSym(use('LtNe', ['0', 'x'], c, [hx])), ny = X.neSym(use('LtNe', ['0', 'y'], c, [hy]));
  const f = [nx, ny];
  const w = '(x^-1 * y^-1)';
  const wp = use('R15', ['x^-1', 'y^-1'], c, [...f, use('InvPos', ['x'], c, [hx]), use('InvPos', ['y'], c, [hy])]);
  const l = use('MulLtPosL', ['x', 'y', w], c, [...f, wp, h]);
  const lx = calc(c, `${w} * x`, [['x * (x^-1 * y^-1)', use('R7', [w, 'x'], c, f)], ['(x * x^-1) * y^-1', X.sym(use('R6', ['x', 'x^-1', 'y^-1'], c, f))],
    ['1 * y^-1', use('R9', ['x'], c, f)], ['y^-1 * 1', use('R7', ['1', 'y^-1'], c, f)], ['y^-1', use('R8', ['y^-1'], c, f)]]);
  const ly = calc(c, `${w} * y`, [[`x^-1 * (y^-1 * y)`, use('R6', ['x^-1', 'y^-1', 'y'], c, f)], ['x^-1 * (y * y^-1)', use('R7', ['y^-1', 'y'], c, f)],
    ['x^-1 * 1', use('R9', ['y'], c, f)], ['x^-1', use('R8', ['x^-1'], c, f)]]);
  return X.rw(ly, X.rw(lx, l, `y^-1 < ${w} * y`, c), 'y^-1 < x^-1', c);
}));
prove('InvLe', 'all x. all y. (x in Real -> y in Real -> 0 < x -> x <= y -> y^-1 <= x^-1)', '[E20]', () => intro(['x', 'y'], ['0 < x', 'x <= y'], (c, [hx, h]) => {
  const hy = use('LtLeTrans', ['0', 'x', 'y'], c, [hx, h]);
  const nx = X.neSym(use('LtNe', ['0', 'x'], c, [hx])), ny = X.neSym(use('LtNe', ['0', 'y'], c, [hy]));
  const lt = X.assume(c, 'x < y', (h1, c1) => X.tc(c1, [use('InvLt', ['x', 'y'], c1, [nx, ny, hx, h1])], 'y^-1 <= x^-1'));
  const eq = X.assume(c, 'x = y', (h1, c1) => X.rw(h1, X.tc(c1, [X.refl('x^-1')], 'x^-1 <= x^-1'), 'y^-1 <= x^-1', c1));
  return X.tc(c, [h, lt, eq], 'y^-1 <= x^-1');
}));
// x^{-1} - y^{-1} = (y - x) · (x^{-1} y^{-1})
prove('SubInv', 'all x. all y. (x in Real -> y in Real -> x != 0 -> y != 0 -> x^-1 - y^-1 = (y - x) * (x^-1 * y^-1))', '[E21]', () => intro(['x', 'y'], ['x != 0', 'y != 0'], (c, [hx, hy]) => {
  const f = [hx, hy], w = '(x^-1 * y^-1)';
  const a = calc(c, `y * ${w}`, [['y * (y^-1 * x^-1)', use('R7', ['x^-1', 'y^-1'], c, f)], ['(y * y^-1) * x^-1', X.sym(use('R6', ['y', 'y^-1', 'x^-1'], c, f))],
    ['1 * x^-1', use('R9', ['y'], c, f)], ['x^-1 * 1', use('R7', ['1', 'x^-1'], c, f)], ['x^-1', use('R8', ['x^-1'], c, f)]]);
  const b = calc(c, `x * ${w}`, [['(x * x^-1) * y^-1', X.sym(use('R6', ['x', 'x^-1', 'y^-1'], c, f))], ['1 * y^-1', use('R9', ['x'], c, f)],
    ['y^-1 * 1', use('R7', ['1', 'y^-1'], c, f)], ['y^-1', use('R8', ['y^-1'], c, f)]]);
  return calc(c, 'x^-1 - y^-1', [[`y * ${w} - y^-1`, X.sym(a)], [`y * ${w} - x * ${w}`, X.sym(b)],
    [`${w} * y - x * ${w}`, use('R7', ['y', w], c, f)], [`${w} * y - ${w} * x`, use('R7', ['x', w], c, f)],
    [`${w} * (y - x)`, use('MulSub', [w, 'y', 'x'], c, f)], [`(y - x) * ${w}`, use('R7', [w, 'y - x'], c, f)]]);
}));
// x · x^{-1} = 1 の別形, x^{-1} x = 1
prove('InvMulL', 'all x. (x in Real -> x != 0 -> x^-1 * x = 1)', '[E22]', () => intro(['x'], ['x != 0'], (c, [hx]) =>
  calc(c, 'x^-1 * x', [['x * x^-1', use('R7', ['x^-1', 'x'], c, [hx])], ['1', use('R9', ['x'], c, [hx])]])));
// (x y^{-1}) y = x
prove('DivMul', 'all x. all y. (x in Real -> y in Real -> y != 0 -> (x * y^-1) * y = x)', '[E23]', () => intro(['x', 'y'], ['y != 0'], (c, [hy]) =>
  calc(c, '(x * y^-1) * y', [['x * (y^-1 * y)', use('R6', ['x', 'y^-1', 'y'], c, [hy])], ['x * 1', use('InvMulL', ['y'], c, [hy])], ['x', use('R8', ['x'], c)]])));
// 0 < y, x < z·y  →  x y^{-1} < z
prove('LtDiv', 'all x. all y. all z. (x in Real -> y in Real -> z in Real -> 0 < y -> x < z * y -> x * y^-1 < z)', '[E24]', () => intro(['x', 'y', 'z'], ['0 < y', 'x < z * y'], (c, [hy, h]) => {
  const ny = X.neSym(use('LtNe', ['0', 'y'], c, [hy]));
  const l = use('MulLtPos', ['x', 'z * y', 'y^-1'], c, [ny, use('InvPos', ['y'], c, [hy]), h]);
  const e = calc(c, '(z * y) * y^-1', [['z * (y * y^-1)', use('R6', ['z', 'y', 'y^-1'], c, [ny])], ['z * 1', use('R9', ['y'], c, [ny])], ['z', use('R8', ['z'], c)]]);
  return X.rw(e, l, 'x * y^-1 < z', c);
}));
// 0 < y, x·y < z → x < z y^{-1}
prove('MulLtDiv', 'all x. all y. all z. (x in Real -> y in Real -> z in Real -> 0 < y -> x * y < z -> x < z * y^-1)', '[E25]', () => intro(['x', 'y', 'z'], ['0 < y', 'x * y < z'], (c, [hy, h]) => {
  const ny = X.neSym(use('LtNe', ['0', 'y'], c, [hy]));
  const l = use('MulLtPos', ['x * y', 'z', 'y^-1'], c, [ny, use('InvPos', ['y'], c, [hy]), h]);
  const e = calc(c, '(x * y) * y^-1', [['x * (y * y^-1)', use('R6', ['x', 'y', 'y^-1'], c, [ny])], ['x * 1', use('R9', ['y'], c, [ny])], ['x', use('R8', ['x'], c)]]);
  return X.rw(e, l, 'x < z * y^-1', c);
}));
// 下からの評価: |x - β| < |β|/2 → |β|/2 < |x|
prove('AbsLowerHalf', 'all x. all be. (x in Real -> be in Real -> abs(x - be) < abs(be) * 2^-1 -> abs(be) * 2^-1 < abs(x))', '[E26]', () => intro(['x', 'be'], ['abs(x - be) < abs(be) * 2^-1'], (c, [h]) => {
  const d = 'abs(be) * 2^-1';
  const t = X.rw(use('SubAdd', ['be', 'x'], c), use('Triangle', ['be - x', 'x'], c), 'abs(be) <= abs(be - x) + abs(x)', c);
  const h2 = X.rw(use('AbsSubComm', ['x', 'be'], c), h, `abs(be - x) < ${d}`, c);
  const s = use('AddLtLe', ['abs(be - x)', d, 'abs(x)', 'abs(x)'], c, [h2, X.tc(c, [X.refl('abs(x)')], 'abs(x) <= abs(x)')]);
  const l = use('LeLtTrans', ['abs(be)', 'abs(be - x) + abs(x)', `${d} + abs(x)`], c, [t, s]);
  const l2 = X.rw(X.sym(use('HalfSum', ['abs(be)'], c)), l, `${d} + ${d} < ${d} + abs(x)`, c);
  const l3 = X.rw(use('R3', [d, d], c), X.rw(use('R3', [d, 'abs(x)'], c), l2, `${d} + ${d} < abs(x) + ${d}`, c), `${d} + ${d} < abs(x) + ${d}`, c);
  return use('LtAddCancel', [d, 'abs(x)', d], c, [l3]);
}));
// 逆三角不等式 ||x| - |y|| ≤ |x - y|
prove('RevTriangle', 'all x. all y. (x in Real -> y in Real -> abs(abs(x) - abs(y)) <= abs(x - y))', '[E27]', () => intro(['x', 'y'], [], (c) => {
  const ax = 'abs(x)', ay = 'abs(y)', d = 'abs(x - y)';
  // |x| ≤ |x - y| + |y|
  const t1 = X.rw(use('SubAdd', ['x', 'y'], c), use('Triangle', ['x - y', 'y'], c), `${ax} <= ${d} + ${ay}`, c);
  const t2 = X.rw(use('SubAdd', ['y', 'x'], c), use('Triangle', ['y - x', 'x'], c), `${ay} <= abs(y - x) + ${ax}`, c);
  const t2b = X.rw(use('AbsSubComm', ['y', 'x'], c), t2, `${ay} <= ${d} + ${ax}`, c);
  // |x| - |y| ≤ d
  const sub = (l, u, v, w) => { // u ≤ w + v  →  u - v ≤ w
    const a = use('LeAddRight', [u, `${w} + ${v}`, `-${v}`], c, [l]);
    const e = calc(c, `(${w} + ${v}) + -${v}`, [[`${w} + (${v} + -${v})`, use('R2', [w, v, `-${v}`], c)], [`${w} + 0`, use('R5', [v], c)], [w, use('R4', [w], c)]]);
    return X.rw(X.sym(X.inst(X.defAx('minus'), [u, v])), X.rw(e, a, `${u} + -${v} <= ${w}`, c), `${u} - ${v} <= ${w}`, c);
  };
  const r1 = sub(t1, ax, ay, d);            // |x| - |y| ≤ d
  const r2 = sub(t2b, ay, ax, d);           // |y| - |x| ≤ d
  const r2b = X.rw(X.sym(use('SubNeg', [ay, ax], c)), r2, `-(${ax} - ${ay}) <= ${d}`, c); // -(|x|-|y|) ≤ d  (SubNeg: -(y - x) = x - y)
  const r3 = use('NegLe', [`-(${ax} - ${ay})`, d], c, [r2b]);
  const r4 = X.rw(use('NegNeg', [`${ax} - ${ay}`], c), r3, `-${d} <= ${ax} - ${ay}`, c);
  return use('LeAbs', [`${ax} - ${ay}`, d], c, [r4, r1]);
}));

module.exports = {};
