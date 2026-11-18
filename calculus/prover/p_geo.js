'use strict';
// テキスト第3章 3節: 累乗と等比数列の極限 (命題3.1)
const K = require('./kit');
const { X, C, prove, intro, use, calc, P, T } = K;
const { fthm } = require('./theory');
const L = require('./lang');
const TX = require('./latex');
const { indNat } = require('./p_nat');
require('./p_seq4'); require('./p_ivt');
const { Rel } = C;

// ---------------- 記号: 累乗の列 pw(r) = (r^n)_{n∈ℕ} ----------------
L.defFunc('pw', 1, a => `{(${a[0]})^{\\bullet}}`);
TX.appHook.set('pw', (as, n) => `{{${TX.texT(as[0], 100)}}^{${TX.texT(n)}}}`);
fthm('PowSeq', 'all r. (r in Real -> Seq(pw(r)) & pw(r)[onew] = r & all n. (n in Nat -> pw(r)[S(n)] = pw(r)[n] * r))', '[S24]', '再帰的定義');
K.seqHooks.set('pw', (ctx, a, facts) => X.tc(ctx, [use('PowSeq', [a.a[0]], ctx, facts)], Rel('Seq', a)));

// ---------------- 補助手続き ----------------
// c ⊢ ∀n (n∈ℕ → E(n)) と c ⊢ t∈ℕ から c ⊢ E(t)
function atN(c, line, t, ht) { const i = X.inst(line, [T(t)]); return X.tc(c, [i, ht], i.phi.b); }
// c ⊢ A ∧ … ∧ ∀n (n∈ℕ → E(n)) から c ⊢ E(t)
function at(c, line, t, ht) { let f = line.phi; while (f.k === 'and') f = f.b; return atN(c, X.tc(c, [line], f), t, ht); }
const powOne = (c, r, facts = []) => X.tc(c, [use('PowSeq', [r], c, facts)], `pw(${r})[onew] = ${r}`);
const powS = (c, r, n, hn, facts = []) => at(c, use('PowSeq', [r], c, facts), n, hn);
const seqOf = (c, a, facts = []) => K.findFact(c, `Seq(${a})`, facts) ?? X.tc(c, [use('PowSeq', [T(a).a[0]], c, facts)], `Seq(${a})`);

// ∀vars (vars ∈ ℝ → hyps → ∀n (n ∈ ℕ → φ(n))) を帰納法で示す
//   base(ctx, hs) : ctx ⊢ φ(1_ω),  step(c, hs, hn, hp) : c ⊢ φ(S n)
function natThm(name, label, vars, hyps, phi, base, step) {
  const hs = [...vars.map(v => v + ' in Real'), ...hyps];
  const stmt = `${vars.map(x => 'all ' + x + '. ').join('')}(${hs.map(h => h + ' -> ').join('')}all n. (n in Nat -> ${phi('n')}))`;
  return prove(name, stmt, label, () => {
    const rec = (i, ctx, ls) => i < hs.length ? X.assume(ctx, hs[i], (h, c) => rec(i + 1, c, [...ls, h])) :
      indNat(ctx, 'n', phi('n'), base(ctx, ls), (c2, n, hn, hp) => step(c2, ls, hn, hp));
    return X.genAll(rec(0, [], []), vars);
  });
}

// ---------------- 体の補題 ----------------
prove('MulZeroCancel', 'all x. all y. (x in Real -> y in Real -> y != 0 -> x * y = 0 -> x = 0)', '[E48]', () => intro(['x', 'y'], ['y != 0', 'x * y = 0'], (c, [hy, he]) =>
  calc(c, 'x', [['x * 1', use('R8', ['x'], c)], ['x * (y * y^-1)', use('R9', ['y'], c, [hy])], ['(x * y) * y^-1', use('R6', ['x', 'y', 'y^-1'], c, [hy])],
    ['0 * y^-1', he], ['y^-1 * 0', use('R7', ['0', 'y^-1'], c, [hy])], ['0', use('Mul0', ['y^-1'], c, [hy])]])));

// ---------------- 累乗の基本性質 ----------------
natThm('PowAbs', '[P1]', ['r'], [], n => `abs(pw(r)[${n}]) = pw(abs(r))[${n}]`,
  c => calc(c, 'abs(pw(r)[onew])', [['abs(r)', powOne(c, 'r')], ['pw(abs(r))[onew]', powOne(c, 'abs(r)')]]),
  (c, hs, hn, hp) => calc(c, 'abs(pw(r)[S(n)])', [['abs(pw(r)[n] * r)', powS(c, 'r', 'n', hn)], ['abs(pw(r)[n]) * abs(r)', use('AbsMul', ['pw(r)[n]', 'r'], c, [hn])],
    ['pw(abs(r))[n] * abs(r)', hp], ['pw(abs(r))[S(n)]', powS(c, 'abs(r)', 'n', hn)]]));
natThm('PowNonneg', '[P2]', ['r'], ['0 <= r'], n => `0 <= pw(r)[${n}]`,
  (c, hs) => X.rw(X.sym(powOne(c, 'r')), hs[1], '0 <= pw(r)[onew]', c),
  (c, hs, hn, hp) => X.rw(X.sym(powS(c, 'r', 'n', hn)), use('MulNonneg', ['pw(r)[n]', 'r'], c, [hn, hp, hs[1]]), '0 <= pw(r)[S(n)]', c));
natThm('PowPos', '[P3]', ['r'], ['0 < r'], n => `0 < pw(r)[${n}]`,
  (c, hs) => X.rw(X.sym(powOne(c, 'r')), hs[1], '0 < pw(r)[onew]', c),
  (c, hs, hn, hp) => X.rw(X.sym(powS(c, 'r', 'n', hn)), use('MulPosPos', ['pw(r)[n]', 'r'], c, [hn, hp, hs[1]]), '0 < pw(r)[S(n)]', c));
natThm('PowNe0', '[P4]', ['r'], ['r != 0'], n => `pw(r)[${n}] != 0`,
  (c, hs) => X.rw(X.sym(powOne(c, 'r')), hs[1], 'pw(r)[onew] != 0', c),
  (c, hs, hn, hp) => X.rw(X.sym(powS(c, 'r', 'n', hn)), use('MulNe0', ['pw(r)[n]', 'r'], c, [hn, hp, hs[1]]), 'pw(r)[S(n)] != 0', c));
natThm('PowOneOne', '[P5]', [], [], n => `pw(1)[${n}] = 1`,
  c => powOne(c, '1'),
  (c, hs, hn, hp) => calc(c, 'pw(1)[S(n)]', [['pw(1)[n] * 1', powS(c, '1', 'n', hn)], ['pw(1)[n]', use('R8', ['pw(1)[n]'], c, [hn])], ['1', hp]]));
natThm('PowInv', '[P6]', ['r'], ['r != 0'], n => `pw(r^-1)[${n}] = pw(r)[${n}]^-1`,
  (c, hs) => calc(c, 'pw(r^-1)[onew]', [['r^-1', powOne(c, 'r^-1', [hs[1]])], ['pw(r)[onew]^-1', powOne(c, 'r')]]),
  (c, hs, hn, hp) => {
    const nz = atN(c, use('PowNe0', ['r'], c, [hs[1]]), 'n', hn);
    const f = [hn, nz, hs[1]];
    return calc(c, 'pw(r^-1)[S(n)]', [['pw(r^-1)[n] * r^-1', powS(c, 'r^-1', 'n', hn, f)], ['pw(r)[n]^-1 * r^-1', hp],
      ['(pw(r)[n] * r)^-1', use('InvMul', ['pw(r)[n]', 'r'], c, f)], ['pw(r)[S(n)]^-1', powS(c, 'r', 'n', hn)]]);
  });

prove('PowDec', 'all r. (r in Real -> 0 <= r -> r <= 1 -> MonoDec(pw(r)))', '[P7]', () => intro(['r'], ['0 <= r', 'r <= 1'], (c, [h0, h1]) => {
  const all = X.gen(X.assume(c, 'n in Nat', (hn, c2) => {
    const nn = atN(c2, use('PowNonneg', ['r'], c2, [h0]), 'n', hn);
    const le = use('MulLeNonnegL', ['r', '1', 'pw(r)[n]'], c2, [hn, nn, h1]);
    const a = X.rw(X.sym(powS(c2, 'r', 'n', hn)), le, 'pw(r)[S(n)] <= pw(r)[n] * 1', c2);
    return X.rw(use('R8', ['pw(r)[n]'], c2, [hn]), a, 'pw(r)[S(n)] <= pw(r)[n]', c2);
  }), 'n');
  return X.tc(c, [X.inst(X.defAx('MonoDec'), ['pw(r)']), seqOf(c, 'pw(r)'), all], 'MonoDec(pw(r))');
}));

// ---------------- 列をひとつずらす ----------------
prove('SucIdx', 'SubIdx(sucf)', '[C28]', () => {
  const all = X.gen(X.assume([], 'k in Nat', (hk, c) => {
    const sk = use('NatS', ['k'], c, [hk]);
    const v1 = at(c, X.thm('Sucf'), 'k', hk), v2 = at(c, X.thm('Sucf'), 'S(k)', sk);
    const lt = use('LtS', ['S(k)'], c, [use('NatOmega', ['S(k)'], c, [sk])]);
    return X.rw(X.sym(v2), X.rw(X.sym(v1), lt, 'sucf[k] < S(S(k))', c), 'sucf[k] < sucf[S(k)]', c);
  }), 'k');
  return X.tc([], [X.inst(X.defAx('SubIdx'), ['sucf']), X.thm('Sucf'), all], 'SubIdx(sucf)');
});

// ---------------- 命題3.1 (等比数列の極限) ----------------
prove('GeoLim', 'all r. (r in Real -> abs(r) < 1 -> Conv(pw(r), 0))', '命題3.1(3)', () => intro(['r'], ['abs(r) < 1'], (c, [h1]) => {
  const s = 'abs(r)', ps = `pw(${s})`;
  const s0 = use('AbsNonneg', ['r'], c);
  const md = use('PowDec', [s], c, [s0, X.tc(c, [h1], `${s} <= 1`)]);
  const lb = use('PowNonneg', [s], c, [s0]);
  return X.exE(use('MonoConvDec', [ps, '0'], c, [md, lb]), 'L', (hL, cL) => {
    const Lr = use('ConvR', [ps, 'L'], cL, [hL]);
    const seqS = seqOf(cL, ps);
    const c1 = use('SubConvIdx', [ps, 'sucf', 'L'], cL, [hL, X.thm('SucIdx')]);
    const c2 = use('LimScalar', [s, ps, 'L'], cL, [hL]);
    const nsq = X.tc(cL, [X.thm('Sucf')], 'NSeq(sucf)');
    const sb = use('SubSeqF', [ps, 'sucf'], cL, [seqS, nsq]);
    const seqB = X.tc(cL, [sb], `Seq(sseq(${ps},sucf))`);
    const eqAll = X.gen(X.assume(cL, 'n in Nat', (hn, cn) => calc(cn, `odot(${s},${ps})[n]`, [
      [`${s} * ${ps}[n]`, at(cn, use('Odot', [s, ps], cn, [seqS]), 'n', hn)],
      [`${ps}[n] * ${s}`, use('R7', [s, `${ps}[n]`], cn, [hn])],
      [`${ps}[S(n)]`, powS(cn, s, 'n', hn)],
      [`${ps}[sucf[n]]`, at(cn, X.thm('Sucf'), 'n', hn)],
      [`sseq(${ps},sucf)[n]`, at(cn, sb, 'n', hn)]])), 'n');
    const c3 = use('ConvExt', [`odot(${s},${ps})`, `sseq(${ps},sucf)`, `${s} * L`], cL, [seqB, eqAll, c2]);
    const eqL = use('LimUnique', [`sseq(${ps},sucf)`, 'L', `${s} * L`], cL, [c1, c3]);
    const z = calc(cL, `L * (1 - ${s})`, [[`L * 1 - L * ${s}`, use('MulSub', ['L', '1', s], cL, [Lr])], [`L - L * ${s}`, use('R8', ['L'], cL, [Lr])],
      [`L - ${s} * L`, use('R7', ['L', s], cL, [Lr])], ['L - L', eqL], ['0', use('SubSelf', ['L'], cL, [Lr])]]);
    const ne = X.neSym(use('LtNe', ['0', `1 - ${s}`], cL, [use('SubPos', [s, '1'], cL, [h1])]));
    const L0 = use('MulZeroCancel', ['L', `1 - ${s}`], cL, [Lr, ne, z]);
    const cs0 = X.rw(L0, hL, `Conv(${ps}, 0)`, cL);
    const seqR = seqOf(cL, 'pw(r)');
    const aq = use('AbsSeq', ['pw(r)'], cL, [seqR]);
    const eq2 = X.gen(X.assume(cL, 'n in Nat', (hn, cn) => calc(cn, `${ps}[n]`, [['abs(pw(r)[n])', atN(cn, use('PowAbs', ['r'], cn), 'n', hn)],
      ['absq(pw(r))[n]', at(cn, aq, 'n', hn)]])), 'n');
    const c4 = use('ConvExt', [ps, 'absq(pw(r))', '0'], cL, [X.tc(cL, [aq], 'Seq(absq(pw(r)))'), eq2, cs0]);
    return X.tc(cL, [use('LimAbsZero', ['pw(r)'], cL, [seqR]), c4], 'Conv(pw(r), 0)');
  }, c);
}));

prove('GeoOne', 'Conv(pw(1), 1)', '命題3.1(2)', () => {
  const c = [];
  const cc = use('ConstConv', ['1'], c);
  const cs = use('ConstSeq', ['1'], c);
  const eq = X.gen(X.assume(c, 'n in Nat', (hn, cn) => calc(cn, 'cseq(1)[n]', [['1', at(cn, cs, 'n', hn)], ['pw(1)[n]', atN(cn, X.thm('PowOneOne'), 'n', hn)]])), 'n');
  return use('ConvExt', ['cseq(1)', 'pw(1)', '1'], c, [seqOf(c, 'pw(1)'), eq, cc]);
});

prove('GeoDvg', 'all r. (r in Real -> 1 < r -> DvgP(pw(r)))', '命題3.1(1)', () => intro(['r'], ['1 < r'], (c, [h1]) => {
  const rp = use('LtTrans', ['0', '1', 'r'], c, [X.thm('ZeroLtOne'), h1]);
  const rn = X.neSym(use('LtNe', ['0', 'r'], c, [rp]));
  const f = [rn];
  const q = 'r^-1', pq = `pw(${q})`;
  const qp = use('InvPos', ['r'], c, [rp]);
  const qlt = X.rw(X.thm('Inv1'), use('InvLt', ['1', 'r'], c, [X.thm('ZeroLtOne'), h1]), 'r^-1 < 1', c);
  const aq = X.rw(X.sym(use('AbsOfNonneg', [q], c, [rn, use('PosNonneg', [q], c, [qp])])), qlt, 'abs(r^-1) < 1', c);
  const conv0 = use('GeoLim', [q], c, [rn, aq]);
  const pos = use('PowPos', [q], c, [rn, qp]);
  const dv = use('RecipDvg', [pq], c, [pos, conv0]);
  const nz = X.gen(X.assume(c, 'n in Nat', (hn, cn) => X.neSym(use('LtNe', ['0', `${pq}[n]`], cn, [atN(cn, pos, 'n', hn)]))), 'n');
  const rc = use('Recip', [pq], c, [seqOf(c, pq, f), nz]);
  const le = X.gen(X.assume(c, 'n in Nat', (hn, cn) => {
    const nz2 = atN(cn, use('PowNe0', ['r'], cn, [rn]), 'n', hn);
    const e = calc(cn, `recip(${pq})[n]`, [[`${pq}[n]^-1`, at(cn, rc, 'n', hn)], ['(pw(r)[n]^-1)^-1', atN(cn, use('PowInv', ['r'], cn, [rn]), 'n', hn)],
      ['pw(r)[n]', use('InvInv', ['pw(r)[n]'], cn, [hn, nz2])]]);
    return X.tc(cn, [e], `recip(${pq})[n] <= pw(r)[n]`);
  }), 'n');
  return use('DvgLe', [`recip(${pq})`, 'pw(r)'], c, [dv, seqOf(c, 'pw(r)'), le]);
}));

module.exports = { atN, at, natThm, powOne, powS, seqOf };
