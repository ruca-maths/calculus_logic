'use strict';
// テキスト第3章 4節: 級数 (定義4.1, 命題4.3, 定理4.4, 定理4.7)
const K = require('./kit');
const { X, C, prove, intro, use, calc, mem, P, T } = K;
const { fthm } = require('./theory');
const L = require('./lang');
const TX = require('./latex');
const { indNat } = require('./p_nat');
const { atN, at, powOne, powS } = require('./p_geo');
const { Rel, F, V } = C;

// ---------------- 記号: 部分和の列 psum(a) = (Σ_{k=1}^n a_k)_{n∈ℕ} ----------------
L.defFunc('psum', 1, a => `\\Sigma ${a[0]}`);
TX.appHook.set('psum', (as, n) => `{\\textstyle\\sum_{k=1}^{${TX.texT(n)}} ${TX.texT(F('app', as[0], V('k')))}}`);
fthm('PSum', 'all a. (Seq(a) -> Seq(psum(a)) & psum(a)[onew] = a[onew] & all n. (n in Nat -> psum(a)[S(n)] = psum(a)[n] + a[S(n)]))', '[S25]', '再帰的定義');
// ω の元は ∅ でなければ後者 (第4章)
fthm('Pred', 'all n. (n in Nat -> n != onew -> ex m. (m in Nat & n = S(m)))', '[N18]', '定理(ωの順序)');

// ---------------- 列であることの証明 (項の形に従って) ----------------
const nsucf = c => X.tc(c, [X.thm('Sucf')], 'NSeq(sucf)');
function seqOf(c, t, facts = []) {
  t = T(t);
  const g = Rel('Seq', t);
  const hit = K.findFact(c, g, facts); if (hit) return hit;
  if (t.k !== 'app') throw new Error('seqOf: ' + C.showT(t));
  const A = t.a;
  switch (t.f) {
    case 'pw': return X.tc(c, [use('PowSeq', [A[0]], c, facts)], g);
    case 'psum': return X.tc(c, [use('PSum', [A[0]], c, [seqOf(c, A[0], facts), ...facts])], g);
    case 'oplus': return X.tc(c, [use('Oplus', A, c, [seqOf(c, A[0], facts), seqOf(c, A[1], facts)])], g);
    case 'odot': return X.tc(c, [use('Odot', A, c, [seqOf(c, A[1], facts), ...facts])], g);
    case 'cseq': return X.tc(c, [use('ConstSeq', A, c, facts)], g);
    case 'absq': return X.tc(c, [use('AbsSeq', A, c, [seqOf(c, A[0], facts)])], g);
    case 'sseq': return X.tc(c, [use('SubSeqF', A, c, [seqOf(c, A[0], facts), nsucf(c)])], g);
  }
  throw new Error('seqOf: ' + C.showT(t));
}
for (const g of ['psum', 'oplus', 'odot', 'cseq', 'absq', 'sseq']) K.seqHooks.set(g, (ctx, a, facts) => seqOf(ctx, a, facts));
// 項の値: t[n] = … (t は oplus, odot, cseq, absq, sseq(_, sucf))
function val(c, t, n, hn, facts = []) {
  t = T(t); const A = t.a;
  switch (t.f) {
    case 'oplus': return at(c, use('Oplus', A, c, [seqOf(c, A[0], facts), seqOf(c, A[1], facts)]), n, hn);
    case 'odot': return at(c, use('Odot', A, c, [seqOf(c, A[1], facts), ...facts]), n, hn);
    case 'cseq': return at(c, use('ConstSeq', A, c, facts), n, hn);
    case 'absq': return at(c, use('AbsSeq', A, c, [seqOf(c, A[0], facts)]), n, hn);
    case 'sseq': {  // a[sucf[n]] = a[S(n)] まで
      const l = at(c, use('SubSeqF', A, c, [seqOf(c, A[0], facts), nsucf(c)]), n, hn);
      return X.trans(l, K.cong(at(c, X.thm('Sucf'), n, hn), C.F('app', A[0], C.F('app', F('sucf'), T(n))), c), c);
    }
  }
  throw new Error('val: ' + C.showT(t));
}
const psumOne = (c, a, facts = []) => X.tc(c, [use('PSum', [a], c, [seqOf(c, a, facts)])], `psum(${a})[onew] = ${a}[onew]`);
const psumS = (c, a, n, hn, facts = []) => at(c, use('PSum', [a], c, [seqOf(c, a, facts)]), n, hn);

// ∀vars (hyps → ∀n (n ∈ ℕ → φ(n))) を帰納法で示す (vars に ∈ℝ は付けない)
function indThm(name, label, vars, hyps, phi, base, step) {
  const stmt = `${vars.map(x => 'all ' + x + '. ').join('')}(${hyps.map(h => h + ' -> ').join('')}all n. (n in Nat -> ${phi('n')}))`;
  return prove(name, stmt, label, () => {
    const rec = (i, ctx, ls) => i < hyps.length ? X.assume(ctx, hyps[i], (h, c) => rec(i + 1, c, [...ls, h])) :
      indNat(ctx, 'n', phi('n'), base(ctx, ls), (c2, n, hn, hp) => step(c2, ls, hn, hp));
    return X.genAll(rec(0, [], []), vars);
  });
}
// 収束の定義の導入
const convDef = (a, al) => X.inst(X.defAx('Conv'), [T(a), T(al)]);
function tailIntro(c, Nt, nNat, goal, body) {
  const b = X.assume(c, 'n in Nat', (hn, cn) => X.assume(cn, `${Nt} <= n`, (hl, cl) => body(cl, hn, hl)));
  const G = N => `${N} in Nat & all n. (n in Nat -> ${N} <= n -> ${goal('n')})`;
  return X.exI(X.tc(c, [nNat, X.gen(b, 'n')], G(Nt)), 'N', G('N'), Nt);
}
const tailAt = (c, hN, N, goal, n, hn, hl) => X.tc(c, [X.inst(X.tc(c, [hN], `all n. (n in Nat -> ${N} <= n -> ${goal('n')})`), [T(n)]), hn, hl], goal(n));

// ---------------- 体の補題 ----------------
prove('AddSwap4', 'all x. all y. all u. all v. (x in Real -> y in Real -> u in Real -> v in Real -> (x + y) + (u + v) = (x + u) + (y + v))', '[E49]', () =>
  intro(['x', 'y', 'u', 'v'], [], c => calc(c, '(x + y) + (u + v)', [['x + (y + (u + v))', use('R2', ['x', 'y', 'u + v'], c)], ['x + ((y + u) + v)', use('R2', ['y', 'u', 'v'], c)],
    ['x + ((u + y) + v)', use('R3', ['y', 'u'], c)], ['x + (u + (y + v))', use('R2', ['u', 'y', 'v'], c)], ['(x + u) + (y + v)', use('R2', ['x', 'u', 'y + v'], c)]])));
prove('NegOneMul', 'all x. (x in Real -> -1 * x = -x)', '[E50]', () => intro(['x'], [], c => calc(c, '-1 * x', [['-(1 * x)', use('NegMul', ['1', 'x'], c)],
  ['-(x * 1)', use('R7', ['1', 'x'], c)], ['-x', use('R8', ['x'], c)]])));

// ---------------- 列をひとつずらしても極限は変わらない ----------------
prove('ShiftConv', 'all a. all al. (Seq(a) -> Conv(sseq(a,sucf), al) -> Conv(a, al))', '[C29]', () => X.genAll(X.assume([], 'Seq(a)', (sa, k1) => X.assume(k1, 'Conv(sseq(a,sucf), al)', (h, k) => {
  const ar = use('ConvR', ['sseq(a,sucf)', 'al'], k, [h]);
  const all = X.gen(X.assume(k, 'eps in Real', (he, c1) => X.assume(c1, '0 < eps', (hp, c2) => X.exE(use('ConvE', ['sseq(a,sucf)', 'al', 'eps'], c2, [h, he, hp]), 'N', (hN, cN) => {
    const Nn = X.tc(cN, [hN], 'N in Nat'), No = use('NatOmega', ['N'], cN, [Nn]);
    const ltS = use('LtS', ['N'], cN, [No]);
    return tailIntro(cN, 'S(N)', use('NatS', ['N'], cN, [Nn]), n => `abs(a[${n}] - al) < eps`, (cl, hn, hl) => {
      const lt1 = use('LtLeTrans', ['onew', 'S(N)', 'n'], cl, [use('LeLtTrans', ['onew', 'N', 'S(N)'], cl, [use('OneLe', ['N'], cl, [Nn]), ltS]), hl]);
      const ne = X.neSym(use('LtNe', ['onew', 'n'], cl, [lt1]));
      return X.exE(use('Pred', ['n'], cl, [hn, ne]), 'm', (hm, cm) => {
        const mN = X.tc(cm, [hm], 'm in Nat'), eq = X.tc(cm, [hm], 'n = S(m)');
        const hl2 = X.rw(eq, hl, 'S(N) <= S(m)', cm);
        const NSm = use('LeTrans', ['N', 'S(N)', 'S(m)'], cm, [X.inst(X.thm('LeS'), ['N']), hl2]);
        const cs = use('LeSCases', ['N', 'm'], cm, [No, use('NatOmega', ['m'], cm, [mN]), NSm]);
        const bad = X.assume(cm, 'N = S(m)', (h2, c3) => X.tc(c3, [use('LeNotLt', ['S(N)', 'N'], c3, [X.rw(X.sym(h2), hl2, 'S(N) <= N', c3)]), ltS], 'N <= m'));
        const Nm = X.tc(cm, [cs, bad], 'N <= m');
        const v = tailAt(cm, hN, 'N', n => `abs(sseq(a,sucf)[${n}] - al) < eps`, 'm', mN, Nm);
        const e = X.trans(val(cm, 'sseq(a,sucf)', 'm', mN), K.cong(X.sym(eq), 'a[S(m)]', cm), cm);
        return X.rw(e, v, 'abs(a[n] - al) < eps', cm);
      }, cl);
    });
  }, c2))), 'eps');
  return X.tc(k, [convDef('a', 'al'), sa, ar, all], 'Conv(a, al)');
})), ['a', 'al']));

// ---------------- 部分和の線形性 ----------------
indThm('PSumAdd', '[Q1]', ['a', 'b'], ['Seq(a)', 'Seq(b)'], n => `psum(oplus(a,b))[${n}] = psum(a)[${n}] + psum(b)[${n}]`,
  c => {
    const one = X.thm('NatOne');
    return calc(c, 'psum(oplus(a,b))[onew]', [['oplus(a,b)[onew]', psumOne(c, 'oplus(a,b)')], ['a[onew] + b[onew]', val(c, 'oplus(a,b)', 'onew', one)],
      ['psum(a)[onew] + b[onew]', psumOne(c, 'a')], ['psum(a)[onew] + psum(b)[onew]', psumOne(c, 'b')]]);
  },
  (c, hs, hn, hp) => {
    const sn = use('NatS', ['n'], c, [hn]); const f = [hn, sn];
    return calc(c, 'psum(oplus(a,b))[S(n)]', [['psum(oplus(a,b))[n] + oplus(a,b)[S(n)]', psumS(c, 'oplus(a,b)', 'n', hn)],
      ['(psum(a)[n] + psum(b)[n]) + oplus(a,b)[S(n)]', hp], ['(psum(a)[n] + psum(b)[n]) + (a[S(n)] + b[S(n)])', val(c, 'oplus(a,b)', 'S(n)', sn)],
      ['(psum(a)[n] + a[S(n)]) + (psum(b)[n] + b[S(n)])', use('AddSwap4', ['psum(a)[n]', 'psum(b)[n]', 'a[S(n)]', 'b[S(n)]'], c, f)],
      ['psum(a)[S(n)] + (psum(b)[n] + b[S(n)])', psumS(c, 'a', 'n', hn)], ['psum(a)[S(n)] + psum(b)[S(n)]', psumS(c, 'b', 'n', hn)]]);
  });
indThm('PSumScal', '[Q2]', ['l', 'a'], ['l in Real', 'Seq(a)'], n => `psum(odot(l,a))[${n}] = l * psum(a)[${n}]`,
  c => {
    const one = X.thm('NatOne');
    return calc(c, 'psum(odot(l,a))[onew]', [['odot(l,a)[onew]', psumOne(c, 'odot(l,a)')], ['l * a[onew]', val(c, 'odot(l,a)', 'onew', one)], ['l * psum(a)[onew]', psumOne(c, 'a')]]);
  },
  (c, hs, hn, hp) => {
    const sn = use('NatS', ['n'], c, [hn]); const f = [hn, sn];
    return calc(c, 'psum(odot(l,a))[S(n)]', [['psum(odot(l,a))[n] + odot(l,a)[S(n)]', psumS(c, 'odot(l,a)', 'n', hn)],
      ['l * psum(a)[n] + odot(l,a)[S(n)]', hp], ['l * psum(a)[n] + l * a[S(n)]', val(c, 'odot(l,a)', 'S(n)', sn)],
      ['l * (psum(a)[n] + a[S(n)])', use('R10', ['l', 'psum(a)[n]', 'a[S(n)]'], c, f)], ['l * psum(a)[S(n)]', psumS(c, 'a', 'n', hn)]]);
  });

// ---------------- 定理4.4 (収束する級数の和・定数倍) ----------------
prove('SerAdd', 'all a. all b. all s. all t. (Seq(a) -> Seq(b) -> Conv(psum(a), s) -> Conv(psum(b), t) -> Conv(psum(oplus(a,b)), s + t))', '定理4.4(和)', () =>
  X.genAll(X.assume([], 'Seq(a)', (ha, c1) => X.assume(c1, 'Seq(b)', (hb, c2) => X.assume(c2, 'Conv(psum(a), s)', (hs, c3) => X.assume(c3, 'Conv(psum(b), t)', (ht, c) => {
    const l = use('LimSum', ['psum(a)', 's', 'psum(b)', 't'], c, [hs, ht]);
    const eq = X.gen(X.assume(c, 'n in Nat', (hn, cn) => calc(cn, 'oplus(psum(a),psum(b))[n]', [['psum(a)[n] + psum(b)[n]', val(cn, 'oplus(psum(a),psum(b))', 'n', hn)],
      ['psum(oplus(a,b))[n]', atN(cn, use('PSumAdd', ['a', 'b'], cn), 'n', hn)]])), 'n');
    return use('ConvExt', ['oplus(psum(a),psum(b))', 'psum(oplus(a,b))', 's + t'], c, [seqOf(c, 'psum(oplus(a,b))'), eq, l]);
  })))), ['a', 'b', 's', 't']));
prove('SerScal', 'all l. all a. all s. (l in Real -> Seq(a) -> Conv(psum(a), s) -> Conv(psum(odot(l,a)), l * s))', '定理4.4(定数倍)', () =>
  X.genAll(X.assume([], 'l in Real', (hl, c1) => X.assume(c1, 'Seq(a)', (ha, c2) => X.assume(c2, 'Conv(psum(a), s)', (hs, c) => {
    const l = use('LimScalar', ['l', 'psum(a)', 's'], c, [hs]);
    const eq = X.gen(X.assume(c, 'n in Nat', (hn, cn) => calc(cn, 'odot(l,psum(a))[n]', [['l * psum(a)[n]', val(cn, 'odot(l,psum(a))', 'n', hn)],
      ['psum(odot(l,a))[n]', atN(cn, use('PSumScal', ['l', 'a'], cn), 'n', hn)]])), 'n');
    return use('ConvExt', ['odot(l,psum(a))', 'psum(odot(l,a))', 'l * s'], c, [seqOf(c, 'psum(odot(l,a))'), eq, l]);
  }))), ['l', 'a', 's']));

// ---------------- 定理4.7 (級数が収束する必要条件) ----------------
prove('SerTerm', 'all a. all s. (Seq(a) -> Conv(psum(a), s) -> Conv(a, 0))', '定理4.7(1)', () => X.genAll(X.assume([], 'Seq(a)', (ha, c1) => X.assume(c1, 'Conv(psum(a), s)', (hs, c) => {
  const sr = use('ConvR', ['psum(a)', 's'], c, [hs]);
  const sh = 'sseq(psum(a),sucf)', d = `oplus(${sh},odot(-1,psum(a)))`;
  const c1b = use('SubConvIdx', ['psum(a)', 'sucf', 's'], c, [hs, X.thm('SucIdx')]);
  const lim = use('LimSum', [sh, 's', 'odot(-1,psum(a))', '-1 * s'], c, [c1b, use('LimScalar', ['-1', 'psum(a)', 's'], c, [hs])]);
  const z = calc(c, 's + -1 * s', [['s + -s', use('NegOneMul', ['s'], c, [sr])], ['0', use('R5', ['s'], c, [sr])]]);
  const lim0 = X.rw(z, lim, `Conv(${d}, 0)`, c);
  const eq = X.gen(X.assume(c, 'n in Nat', (hn, cn) => {
    const sn = use('NatS', ['n'], cn, [hn]); const f = [hn, sn];
    return calc(cn, `${d}[n]`, [[`${sh}[n] + odot(-1,psum(a))[n]`, val(cn, d, 'n', hn)], ['psum(a)[S(n)] + odot(-1,psum(a))[n]', val(cn, sh, 'n', hn)],
      ['psum(a)[S(n)] + -1 * psum(a)[n]', val(cn, 'odot(-1,psum(a))', 'n', hn)], ['psum(a)[S(n)] + -psum(a)[n]', use('NegOneMul', ['psum(a)[n]'], cn, f)],
      ['(psum(a)[n] + a[S(n)]) + -psum(a)[n]', psumS(cn, 'a', 'n', hn)], ['(a[S(n)] + psum(a)[n]) + -psum(a)[n]', use('R3', ['psum(a)[n]', 'a[S(n)]'], cn, f)],
      ['(a[S(n)] + psum(a)[n]) - psum(a)[n]', X.inst(X.defAx('minus'), [T('a[S(n)] + psum(a)[n]'), T('psum(a)[n]')])],
      ['a[S(n)]', use('AddSub', ['a[S(n)]', 'psum(a)[n]'], cn, f)], ['sseq(a,sucf)[n]', val(cn, 'sseq(a,sucf)', 'n', hn)]]);
  }), 'n');
  const c2 = use('ConvExt', [d, 'sseq(a,sucf)', '0'], c, [seqOf(c, 'sseq(a,sucf)'), eq, lim0]);
  return use('ShiftConv', ['a', '0'], c, [ha, c2]);
})), ['a', 's']));

// ---------------- 命題4.3 (無限等比級数) ----------------
indThm('GeoPartial', '[Q3]', ['r'], ['r in Real'], n => `(1 - r) * psum(pw(r))[${n}] = r - pw(r)[S(${n})]`,
  c => calc(c, '(1 - r) * psum(pw(r))[onew]', [['(1 - r) * pw(r)[onew]', psumOne(c, 'pw(r)')], ['(1 - r) * r', powOne(c, 'r')], ['r * (1 - r)', use('R7', ['1 - r', 'r'], c)],
    ['r * 1 - r * r', use('MulSub', ['r', '1', 'r'], c)], ['r - r * r', use('R8', ['r'], c)], ['r - pw(r)[onew] * r', powOne(c, 'r')],
    ['r - pw(r)[S(onew)]', powS(c, 'r', 'onew', X.thm('NatOne'))]]),
  (c, hs, hn, hp) => {
    const sn = use('NatS', ['n'], c, [hn]); const f = [hn, sn];
    const p = 'pw(r)[S(n)]', q = 'psum(pw(r))[n]';
    return calc(c, '(1 - r) * psum(pw(r))[S(n)]', [[`(1 - r) * (${q} + ${p})`, psumS(c, 'pw(r)', 'n', hn)], [`(1 - r) * ${q} + (1 - r) * ${p}`, use('R10', ['1 - r', q, p], c, f)],
      [`(r - ${p}) + (1 - r) * ${p}`, hp], [`(r - ${p}) + ${p} * (1 - r)`, use('R7', ['1 - r', p], c, f)], [`(r - ${p}) + (${p} * 1 - ${p} * r)`, use('MulSub', [p, '1', 'r'], c, f)],
      [`(r - ${p}) + (${p} - ${p} * r)`, use('R8', [p], c, f)], [`r - ${p} * r`, use('SubSplit', ['r', `${p} * r`, p], c, f)], ['r - pw(r)[S(S(n))]', powS(c, 'r', 'S(n)', sn)]]);
  });
prove('GeoSer', 'all r. (r in Real -> abs(r) < 1 -> Conv(psum(pw(r)), r * (1 - r)^-1))', '命題4.3(1)', () => intro(['r'], ['abs(r) < 1'], (c, [h1]) => {
  const r1 = use('LeLtTrans', ['r', 'abs(r)', '1'], c, [X.tc(c, [use('AbsBound', ['r'], c)], 'r <= abs(r)'), h1]);
  const ne = X.neSym(use('LtNe', ['0', '1 - r'], c, [use('SubPos', ['r', '1'], c, [r1])]));
  const k = '(1 - r)^-1', sh = 'sseq(pw(r),sucf)', d = `oplus(cseq(r),odot(-1,${sh}))`, e = `odot(${k},${d})`;
  const f = [ne];
  const c0 = use('SubConvIdx', ['pw(r)', 'sucf', '0'], c, [use('GeoLim', ['r'], c, [h1]), X.thm('SucIdx')]);
  const l1 = use('LimSum', ['cseq(r)', 'r', `odot(-1,${sh})`, '-1 * 0'], c, [use('ConstConv', ['r'], c), use('LimScalar', ['-1', sh, '0'], c, [c0])]);
  const l2 = use('LimScalar', [k, d, 'r + -1 * 0'], c, [l1, ...f]);
  const eq = X.gen(X.assume(c, 'n in Nat', (hn, cn) => {
    const sn = use('NatS', ['n'], cn, [hn]); const g = [hn, sn, ne];
    const p = 'pw(r)[S(n)]', q = 'psum(pw(r))[n]';
    return calc(cn, `${e}[n]`, [[`${k} * ${d}[n]`, val(cn, e, 'n', hn, f)], [`${k} * (cseq(r)[n] + odot(-1,${sh})[n])`, val(cn, d, 'n', hn)],
      [`${k} * (r + odot(-1,${sh})[n])`, val(cn, 'cseq(r)', 'n', hn)], [`${k} * (r + -1 * ${sh}[n])`, val(cn, `odot(-1,${sh})`, 'n', hn)],
      [`${k} * (r + -1 * ${p})`, val(cn, sh, 'n', hn)], [`${k} * (r + -${p})`, use('NegOneMul', [p], cn, g)],
      [`${k} * (r - ${p})`, X.sym(X.inst(X.defAx('minus'), [T('r'), T(p)]))], [`${k} * ((1 - r) * ${q})`, atN(cn, use('GeoPartial', ['r'], cn), 'n', hn)],
      [`(${k} * (1 - r)) * ${q}`, use('R6', [k, '1 - r', q], cn, g)], [`1 * ${q}`, use('InvMulL', ['1 - r'], cn, g)],
      [`${q} * 1`, use('R7', ['1', q], cn, g)], [q, use('R8', [q], cn, g)]]);
  }), 'n');
  const l3 = use('ConvExt', [e, 'psum(pw(r))', `${k} * (r + -1 * 0)`], c, [seqOf(c, 'psum(pw(r))'), eq, l2]);
  const v = calc(c, `${k} * (r + -1 * 0)`, [[`${k} * (r + 0)`, use('Mul0', ['-1'], c)], [`${k} * r`, use('R4', ['r'], c)], [`r * ${k}`, use('R7', [k, 'r'], c, f)]]);
  return X.rw(v, l3, `Conv(psum(pw(r)), r * ${k})`, c);
}));
// |r| ≥ 1 のとき 1 ≤ |r|^n
indThm('PowGeOne', '[P8]', ['r'], ['r in Real', '1 <= r'], n => `1 <= pw(r)[${n}]`,
  (c, hs) => X.rw(X.sym(powOne(c, 'r')), hs[1], '1 <= pw(r)[onew]', c),
  (c, hs, hn, hp) => {
    const o = X.tc(c, [X.thm('ZeroLtOne')], '0 <= 1');
    const m = use('MulLeLe', ['1', 'pw(r)[n]', '1', 'r'], c, [hn, o, hp, hs[1]]);
    return X.rw(X.sym(powS(c, 'r', 'n', hn)), X.rw(use('R8', ['1'], c), m, '1 <= pw(r)[n] * r', c), '1 <= pw(r)[S(n)]', c);
  });
prove('GeoSerDvg', 'all r. (r in Real -> 1 <= abs(r) -> ~ ex s. Conv(psum(pw(r)), s))', '命題4.3(2)', () => intro(['r'], ['1 <= abs(r)'], (c, [h1]) => {
  const E = 'ex s. Conv(psum(pw(r)), s)';
  const imp = X.assume(c, E, (he, c2) => X.exE(he, 's', (hs, c3) => {
    const sp = seqOf(c3, 'pw(r)');
    const z = use('SerTerm', ['pw(r)', 's'], c3, [sp, hs]);
    const za = X.tc(c3, [use('LimAbsZero', ['pw(r)'], c3, [sp]), z], 'Conv(absq(pw(r)), 0)');
    return X.exE(use('ConvE', ['absq(pw(r))', '0', '1'], c3, [za, X.thm('ZeroLtOne')]), 'N', (hN, cN) => {
      const Nn = X.tc(cN, [hN], 'N in Nat');
      const lt = X.tc(cN, [X.inst(X.tc(cN, [hN], 'all n. (n in Nat -> N <= n -> abs(absq(pw(r))[n] - 0) < 1)'), [T('N')]), Nn, X.tc(cN, [X.refl('N')], 'N <= N')], 'abs(absq(pw(r))[N] - 0) < 1');
      const x = 'pw(abs(r))[N]';
      const ge = atN(cN, use('PowGeOne', ['abs(r)'], cN, [h1]), 'N', Nn);
      const x0 = use('LeTrans', ['0', '1', x], cN, [X.tc(cN, [X.thm('ZeroLtOne')], '0 <= 1'), ge]);
      const e = calc(cN, 'abs(absq(pw(r))[N] - 0)', [['abs(absq(pw(r))[N])', use('SubZero', ['absq(pw(r))[N]'], cN, [Nn])], ['abs(abs(pw(r)[N]))', val(cN, 'absq(pw(r))', 'N', Nn)],
        [`abs(${x})`, atN(cN, use('PowAbs', ['r'], cN), 'N', Nn)], [x, use('AbsOfNonneg', [x], cN, [x0])]]);
      return X.tc(cN, [X.rw(e, lt, `${x} < 1`, cN), use('LeNotLt', ['1', x], cN, [ge])], `~ ${E}`);
    }, c3);
  }, c2));
  return X.tc(c, [imp], `~ ${E}`);
}));

module.exports = { seqOf, val, indThm, psumOne, psumS, tailIntro, tailAt, convDef };
