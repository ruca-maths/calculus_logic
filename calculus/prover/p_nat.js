'use strict';
// 自然数: ℕ の定義, 帰納法の構成手続き, ω の順序と ι の基本性質
const K = require('./kit');
const { X, C, prove, intro, use, calc, mem, P, T } = K;
const { def, fthm } = require('./theory');
require('./p_field');
const { V, F, Rel, All, Ex, Iff, And, Imp, Not, Eq } = C;

def('Nat', 'all n. (n in Nat <-> n in omega & n != emptyset)', 'Def$\\mathbb{N}$');
def('onew', 'onew = S(emptyset)', 'Def$1_\\omega$');

// ---------------------------------------------------------------
//  帰納法の構成手続き (定理「数学的帰納法」の証明をそのまま φ について行う)
//   indOmega(ctx, v, φ, base, step):
//     base : ctx ⊢ φ(∅),   step(c, n, hn, hp) : c ⊢ φ(S n)  (c = ctx + [n∈ω, φ(n)])
//     → ctx ⊢ ∀v (v ∈ ω → φ(v))
// ---------------------------------------------------------------
let indN = 0;
function indOmega(ctx, v, phiS, base, step) {
  const phi = P(phiS);
  const used = new Set(); for (const h of ctx) C.allVars(h, used); C.allVars(phi, used);
  const nm = b => { let s; do { s = b + (++indN); } while (used.has(s)); used.add(s); return s; };
  const B = nm('B'), A = nm('A'), y = v;
  const params = [...C.fv(phi)].filter(z => z !== v);
  const pv = params.map(() => nm('z'));
  let phiP = phi; params.forEach((z, i) => { phiP = C.subst(phiP, z, V(pv[i])); });
  let sep = All(A, Ex(B, All(v, Iff(Rel('in', V(v), V(B)), And(Rel('in', V(v), V(A)), phiP)))));
  for (let i = pv.length - 1; i >= 0; i--) sep = All(pv[i], sep);
  const sepL = X.inst(X.axiom('Sep', sep), [...params.map(z => V(z)), F('omega')]);
  const at = t => C.subst(phi, v, T(t));
  return X.exE(sepL, B, (hB, cB) => {
    const dB = t => X.inst(hB, [T(t)]);
    const oi = X.tc(cB, [X.thm('OmegaInd'), X.inst(X.defAx('Ind'), ['omega'])], 'emptyset in omega & all y. (y in omega -> S(y) in omega)');
    const zB = X.tc(cB, [dB('emptyset'), oi, base], Rel('in', F('emptyset'), V(B)));
    const sB = X.gen(X.assume(cB, Rel('in', V(y), V(B)), (hy, cy) => {
      const yy = X.tc(cy, [dB(V(y)), hy], And(Rel('in', V(y), F('omega')), at(V(y))));
      const hn = X.tc(cy, [yy], Rel('in', V(y), F('omega')));
      const hp = X.tc(cy, [yy], at(V(y)));
      const st = step(cy, V(y), hn, hp);
      const so = X.tc(cy, [X.inst(X.tc(cy, [oi], 'all y. (y in omega -> S(y) in omega)'), [V(y)]), hn], Rel('in', F('S', V(y)), F('omega')));
      return X.tc(cy, [dB(F('S', V(y))), so, st], Rel('in', F('S', V(y)), V(B)));
    }), y);
    const indB = X.tc(cB, [X.inst(X.defAx('Ind'), [V(B)]), zB, sB], Rel('Ind', V(B)));
    return X.gen(X.assume(cB, Rel('in', V(v), F('omega')), (hn, cn) => {
      const all = X.tc(cn, [hn, X.inst(X.defAx('omega'), [V(v)])], All('x', Imp(Rel('Ind', V('x')), Rel('in', V(v), V('x')))));
      return X.tc(cn, [X.inst(all, [V(B)]), indB, dB(V(v))], phi);
    }), v);
  }, ctx);
}

//   indNat(ctx, v, φ, base, step):  base: ctx ⊢ φ(1_ω),  step(c, n, hn: n∈ℕ, hp: φ(n)) : c ⊢ φ(S n)
//     → ctx ⊢ ∀v (v ∈ ℕ → φ(v))
//   (φ'(v) :≡ v ∈ ℕ → φ(v) に indOmega を適用する. v = ∅ のときは S(∅) = 1_ω.)
function indNat(ctx, v, phiS, base, step) {
  const phi = P(phiS);
  const at = t => C.subst(phi, v, T(t));
  const psi = Imp(Rel('in', V(v), F('Nat')), phi);
  const atP = t => C.subst(psi, v, T(t));
  const dNat = t => X.inst(X.defAx('Nat'), [T(t)]);
  const base0 = X.tc(ctx, [dNat('emptyset'), X.refl('emptyset')], atP(F('emptyset')));
  const r = indOmega(ctx, v, psi, base0, (c, n, hn, hp) => X.assume(c, Rel('in', F('S', n), F('Nat')), (hs, c2) => {
    const z = X.assume(c2, Eq(n, F('emptyset')), (he, c3) => {
      const e = X.trans(X.rw(he, X.refl(F('S', n)), Eq(F('S', n), F('S', F('emptyset'))), c3), X.sym(X.defAx('onew')), c3);
      return X.rw(X.sym(e), base, at(F('S', n)), c3);
    });
    const nz = X.assume(c2, Not(Eq(n, F('emptyset'))), (hz, c3) => {
      const nn = X.tc(c3, [dNat(n), hn, hz], Rel('in', n, F('Nat')));
      const pn = X.tc(c3, [hp, nn], at(n));
      return step(c3, n, nn, pn);
    });
    return X.tc(c2, [z, nz], at(F('S', n)));
  }));
  return X.gen(X.assume(ctx, Rel('in', V(v), F('Nat')), (hv, cv) => {
    const vo = X.tc(cv, [hv, dNat(V(v))], Rel('in', V(v), F('omega')));
    return X.tc(cv, [X.inst(r, [V(v)]), vo, hv], phi);
  }), v);
}

// ---------------- ℕ の基本性質 ----------------
const sDef = (x, u) => X.inst(X.defAx('S'), [x, u]);
prove('NatSub', 'Nat sub omega', '[N7]', () => X.tc([], [X.inst(X.defAx('sub'), ['Nat', 'omega']),
  X.gen(X.assume([], 'u in Nat', (h, c) => X.tc(c, [h, X.inst(X.defAx('Nat'), ['u'])], 'u in omega')), 'u')], 'Nat sub omega'));
prove('SNe0', 'all n. S(n) != emptyset', '[N0]', () => X.gen(X.raa([], 'S(n) != emptyset', (h, c) => {
  const e = X.tc(c, [h], 'S(n) = emptyset');
  const m = X.tc(c, [sDef('n', 'n'), X.refl('n')], 'n in S(n)');
  return [X.rw(e, m, 'n in emptyset', c), X.inst(X.defAx('empty'), ['n'])];
}), 'n'));
prove('NatSO', 'all n. (n in omega -> S(n) in Nat)', '[N2$_\omega$]', () => X.gen(X.assume([], 'n in omega', (h, c) => {
  const oi = X.tc(c, [X.thm('OmegaInd'), X.inst(X.defAx('Ind'), ['omega'])], 'all y. (y in omega -> S(y) in omega)');
  return X.tc(c, [X.inst(oi, ['n']), h, X.inst(X.thm('SNe0'), ['n']), X.inst(X.defAx('Nat'), ['S(n)'])], 'S(n) in Nat');
}), 'n'));
prove('NatOne', 'onew in Nat', '[N1]', () => {
  const e = X.tc([], [X.thm('OmegaInd'), X.inst(X.defAx('Ind'), ['omega'])], 'emptyset in omega');
  return X.rw(X.sym(X.defAx('onew')), use('NatSO', ['emptyset'], [], [e]), 'onew in Nat', []);
});
prove('NatS', 'all n. (n in Nat -> S(n) in Nat)', '[N2]', () => X.gen(X.assume([], 'n in Nat', (h, c) => use('NatSO', ['n'], c, [X.tc(c, [h, X.inst(X.defAx('Nat'), ['n'])], 'n in omega')])), 'n'));
prove('NatOmega', 'all n. (n in Nat -> n in omega)', '[N7\']', () => X.gen(X.assume([], 'n in Nat', (h, c) => X.tc(c, [h, X.inst(X.defAx('Nat'), ['n'])], 'n in omega')), 'n'));
prove('LeS', 'all n. n <= S(n)', '[N8]', () => X.gen(X.tc([], [X.inst(X.defAx('lt'), ['n', 'S(n)']), X.inst(X.defAx('sub'), ['n', 'S(n)']),
  X.gen(X.tc([], [sDef('n', 'u')], 'u in n -> u in S(n)'), 'u')], 'n <= S(n)'), 'n'));

// ω の順序 (第4章 定理「ωの順序」から. 通常の証明は本文)
fthm('LeSCases', 'all m. all n. (m in omega -> n in omega -> m <= S(n) -> m <= n | m = S(n))', '[N9]', '定理(ωの順序)');
fthm('LtSLe', 'all m. all n. (m in omega -> n in omega -> m < n -> S(m) <= n)', '[N10]', '定理(ωの順序)');
fthm('OmegaTotal', 'all m. all n. (m in omega -> n in omega -> m <= n | n < m)', '[N11]', '定理(ωの順序)');

// 1_ω ≤ n
prove('OneLe', 'all n. (n in Nat -> onew <= n)', '[N12]', () => indNat([], 'n', 'onew <= n', X.refl('onew') && X.tc([], [X.refl('onew')], 'onew <= onew'),
  (c, n, hn, hp) => use('LeTrans', ['onew', n, F('S', n)], c, [hp, X.inst(X.thm('LeS'), [n])])));

// ι の性質
prove('LtAddOne', 'all x. (x in Real -> x < x + 1)', '[N13]', () => intro(['x'], [], (c) => {
  const l = use('R14', ['0', '1', 'x'], c, [X.thm('ZeroLtOne')]);
  const l1 = X.rw(calc(c, '0 + x', [['x + 0', use('R3', ['0', 'x'], c)], ['x', use('R4', ['x'], c)]]), l, 'x < 1 + x', c);
  return X.rw(use('R3', ['1', 'x'], c), l1, 'x < x + 1', c);
}));
prove('IotaGeOne', 'all n. (n in Nat -> 1 <= iota(n))', '[N14]', () => indNat([], 'n', '1 <= iota(n)', X.tc([], [X.sym(X.thm('Iota1'))], '1 <= iota(onew)'),
  (c, n, hn, hp) => {
    const lt = use('LtAddOne', ['iota(n)'], c, [mem(c, 'iota(n)', [hn])]);
    const le = use('LeLtTrans', ['1', 'iota(n)', 'iota(n) + 1'], c, [hp, lt]);
    return X.tc(c, [X.rw(X.sym(use('IotaS', ['n'], c, [hn])), le, '1 < iota(S(n))', c)], '1 <= iota(S(n))');
  }));
prove('IotaPos', 'all n. (n in Nat -> 0 < iota(n))', '[N15]', () => X.gen(X.assume([], 'n in Nat', (h, c) =>
  use('LtLeTrans', ['0', '1', 'iota(n)'], c, [X.thm('ZeroLtOne'), use('IotaGeOne', ['n'], c, [h])])), 'n'));


// ---------------- 単調性の構成手続き ----------------
// ctx ⊢ m ∈ ℕ のもとで, step(c, n, hn) : c ⊢ R(v(n), v(S n)) (c = ctx+[n∈ℕ]) から
//   ctx ⊢ ∀n (n ∈ ℕ → m ≤ n → R(v(m), v(n)))   (R は ≤ または ≥)
function monoBuild(ctx, m, hm, v, step, dir = 'le') {
  const R = (x, y) => dir === 'le' ? `${x} <= ${y}` : `${y} <= ${x}`;
  const phi = `${m} <= n -> ${R(v(m), v('n'))}`;
  const reflR = (c, t) => X.tc(c, [X.refl(t)], R(t, t));
  const base = X.assume(ctx, `${m} <= onew`, (h, c) => {
    const e = use('LeAntisym', [m, 'onew'], c, [h, use('OneLe', [m], c, [hm])]);
    return X.rw(e, reflR(c, v(m)), R(v(m), v('onew')), c);
  });
  return indNat(ctx, 'n', phi, base, (c, n, hn, hp) => X.assume(c, `${m} <= S(n)`, (h, c2) => {
    const mo = use('NatOmega', [m], c2, [hm]), no = use('NatOmega', ['n'], c2, [hn]);
    const cs = use('LeSCases', [m, 'n'], c2, [mo, no, h]);
    const st = step(c2, 'n', hn);
    const c1 = X.assume(c2, `${m} <= n`, (h1, c3) => {
      const p = X.tc(c3, [hp, h1], R(v(m), v('n')));
      return dir === 'le' ? use('LeTrans', [v(m), v('n'), v('S(n)')], c3, [p, st]) : use('LeTrans', [v('S(n)'), v('n'), v(m)], c3, [st, p]);
    });
    const c2b = X.assume(c2, `${m} = S(n)`, (h1, c3) => X.rw(h1, reflR(c3, v(m)), R(v(m), v('S(n)')), c3));
    return X.tc(c2, [cs, c1, c2b], R(v(m), v('S(n)')));
  }));
}
// ∀vars ∀m ∀n (hyps → m∈ℕ → n∈ℕ → m ≤ n → R(v(m), v(n)))
function monoThm(name, label, vars, hyps, v, step, dir = 'le') {
  const concl = dir === 'le' ? `${v('m')} <= ${v('n')}` : `${v('n')} <= ${v('m')}`;
  const stmt = `${[...vars, 'm', 'n'].map(x => 'all ' + x + '. ').join('')}(${hyps.map(h => h + ' -> ').join('')}m in Nat -> n in Nat -> m <= n -> ${concl})`;
  return prove(name, stmt, label, () => {
    const rec = (i, ctx, hs) => i < hyps.length ? X.assume(ctx, hyps[i], (h, c) => rec(i + 1, c, [...hs, h])) :
      X.assume(ctx, 'm in Nat', (hm, c) => {
        const r = monoBuild(c, 'm', hm, v, (c2, n, hn) => step(c2, hs, hn), dir);
        return X.assume(c, 'n in Nat', (hn, c3) => X.tc(c3, [X.inst(r, ['n']), hn], `m <= n -> ${concl}`));
      });
    return X.genAll(rec(0, [], []), [...vars, 'm', 'n']);
  });
}

monoThm('IotaMono', '[N16]', [], [], t => `iota(${t})`, (c2, hs, hn) => {
  const lt = use('LtAddOne', ['iota(n)'], c2, [mem(c2, 'iota(n)', [hn])]);
  return X.tc(c2, [X.rw(X.sym(use('IotaS', ['n'], c2, [hn])), lt, 'iota(n) < iota(S(n))', c2)], 'iota(n) <= iota(S(n))');
});

module.exports = { indOmega, indNat, monoBuild, monoThm };
