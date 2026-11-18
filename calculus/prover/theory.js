'use strict';
// =====================================================================
//  theory.js — 言語(記号), ZFC の公理, 定義公理, 基礎定理の登録
//  * Def : 定義による拡大の定義公理(第2章)
//  * Thm(status 'F') : 本ノートの本文(第3–5章)で通常の証明を与え,
//                      証明木の葉として用いる基礎定理. 形式的証明木は未作成.
//  * Thm(status 'P') : 本エンジンで完全展開した証明木をもつ定理
// =====================================================================
const C = require('./core');
const L = require('./lang');
const TX = require('./latex');
const { parse } = L;
const { defFunc, defPred } = L;

// ---------------- 記号 ----------------
defFunc('emptyset', 0, () => '\\emptyset');
defFunc('cup', 2, a => `${a[0]} \\cup ${a[1]}`, 50);
defFunc('bigcup', 1, a => `\\textstyle\\bigcup ${a[0]}`, 60);
defFunc('S', 1, a => `S(${a[0]})`);
defFunc('omega', 0, () => '\\omega');
defFunc('Nat', 0, () => '\\mathbb{N}');
defFunc('Real', 0, () => '\\mathbb{R}');
defFunc('Rat', 0, () => '\\mathbb{Q}');
defFunc('0', 0, () => '0');
defFunc('1', 0, () => '1');
defFunc('2', 0, () => '2');
defFunc('onew', 0, () => '1_{\\omega}');
defFunc('iota', 1, a => `\\underline{${a[0]}}`);
defFunc('sup', 1, a => `\\sup ${a[0]}`, 60);
defFunc('inf', 1, a => `\\inf ${a[0]}`, 60);
defFunc('lim', 1, a => `\\lim ${a[0]}`, 60);
defFunc('ArchX', 1, a => `X_{${a[0]}}`);
defFunc('negset', 1, a => `\\ominus ${a[0]}`, 60);
defFunc('oplus', 2, a => `${a[0]} \\oplus ${a[1]}`, 50);
defFunc('otimes', 2, a => `${a[0]} \\otimes ${a[1]}`, 50);
defFunc('odot', 2, a => `${a[0]} \\odot ${a[1]}`, 50);
defFunc('recip', 1, a => `${a[0]}^{\\ast}`, 60);
defFunc('dom', 1, a => `\\mathrm{dom}(${a[0]})`);
defFunc('max2', 2, a => `\\max\\{${a[0]},${a[1]}\\}`);
defFunc('min2', 2, a => `\\min\\{${a[0]},${a[1]}\\}`);
const P1 = name => a => `\\mathrm{${name}}(${a.join(',')})`;
for (const [n, ar] of [['Ind', 1], ['Fnc', 1], ['Seq', 1], ['UB', 2], ['LB', 2], ['IsSup', 2], ['IsInf', 2], ['IsMax', 2], ['IsMin', 2],
  ['BddAb', 1], ['BddBe', 1], ['Bdd', 1], ['Conv', 2], ['Cgt', 1], ['DvgP', 1], ['DvgM', 1], ['Cut', 1], ['SeqBdd', 1],
  ['MonoInc', 1], ['MonoDec', 1], ['Cauchy', 1], ['SubSeq', 2], ['RFn', 1], ['FLim', 3], ['FLimR', 3], ['FLimL', 3], ['FLimInf', 2], ['PNbhd', 2], ['Phi', 1]])
  defPred(n, ar, P1(n));

// 表示上の記法 (記号列の省略として本文で宣言する)
//   x/2 :≡ x · 2^{-1}
TX.addPattern(f => null);
const origTexT = TX.texT;

// ---------------- 登録用関数 ----------------
const registry = [];  // { kind, name, f, label, note }
function axiom(name, s, label, note) { const f = parse(s); C.Theory.axioms.set(name, f); registry.push({ kind: 'Ax', name, f, label, note }); TX.leafLabel.set('Ax:' + name, label ?? name); return f; }
function def(name, s, label, note) { const f = parse(s); C.Theory.defs.set(name, f); registry.push({ kind: 'Def', name, f, label, note }); TX.leafLabel.set('Def:' + name, label ?? name); return f; }
function fthm(name, s, label, note) { const f = parse(s); C.Theory.thms.set(name, { f, status: 'F', note }); registry.push({ kind: 'F', name, f, label, note }); TX.leafLabel.set('Thm:' + name, label ?? name); return f; }

// ---------------- ZFC の公理 (使用するもの) ----------------
axiom('Ext', 'all x. all y. (all z. (z in x <-> z in y)) -> x = y', 'Ext');
C.Theory.schemas.set('Sep', f => {
  // ∀z1…∀zk ∀a ∃y ∀x (x∈y ↔ x∈a ∧ φ),  y ∉ FV(φ)
  let g = f; const outer = [];
  while (g.k === 'all' && g.a.k === 'all') { outer.push(g.v); g = g.a; }
  if (g.k !== 'all') return false;
  const a = g.v, e = g.a; if (e.k !== 'ex') return false;
  const y = e.v, b = e.a; if (b.k !== 'all') return false;
  const x = b.v, c = b.a; if (c.k !== 'iff') return false;
  const l = c.a, r = c.b;
  if (!(l.k === 'rel' && l.r === 'in' && l.a[0].k === 'var' && l.a[0].n === x && l.a[1].k === 'var' && l.a[1].n === y)) return false;
  if (!(r.k === 'and' && r.a.k === 'rel' && r.a.r === 'in' && r.a.a[0].k === 'var' && r.a.a[0].n === x && r.a.a[1].k === 'var' && r.a.a[1].n === a)) return false;
  return !C.fv(r.b).has(y) && y !== a && y !== x;
});
TX.leafLabel.set('Ax:Sep', 'Sep');

// ---------------- 定義公理 ----------------
def('sub', 'all x. all y. (x sub y <-> all u. (u in x -> u in y))', 'Def$\\subseteq$');
def('lt', 'all x. all y. (x < y <-> x sub y & x != y)', 'Def$<$');
def('empty', 'all u. u notin emptyset', 'Def$\\emptyset$');
def('cup', 'all x. all y. all u. (u in cup(x,y) <-> u in x | u in y)', 'Def$\\cup$');
def('bigcup', 'all X. all u. (u in bigcup(X) <-> ex Y. (Y in X & u in Y))', 'Def$\\bigcup$');
def('S', 'all x. all u. (u in S(x) <-> u in x | u = x)', 'Def$S$');
def('Ind', 'all x. (Ind(x) <-> emptyset in x & all y. (y in x -> S(y) in x))', 'DefInd');
def('omega', 'all n. (n in omega <-> all x. (Ind(x) -> n in x))', 'Def$\\omega$');
def('minus', 'all x. all y. x - y = x + -y', 'Def$-$');
def('abs', 'all x. ((0 <= x & abs(x) = x) | (~ 0 <= x & abs(x) = -x))', 'Def$\\lvert\\cdot\\rvert$');
def('two', '2 = 1 + 1', 'Def$2$');
def('UB', 'all a. all X. (UB(a,X) <-> a in Real & all x. (x in X -> x <= a))', 'DefUB');
def('LB', 'all a. all X. (LB(a,X) <-> a in Real & all x. (x in X -> a <= x))', 'DefLB');
def('IsSup', 'all s. all X. (IsSup(s,X) <-> UB(s,X) & all w. (UB(w,X) -> s <= w))', 'DefSup');
def('IsInf', 'all s. all X. (IsInf(s,X) <-> LB(s,X) & all w. (LB(w,X) -> w <= s))', 'DefInf');
def('BddAb', 'all X. (BddAb(X) <-> ex a. UB(a,X))', 'DefBddAb');
def('BddBe', 'all X. (BddBe(X) <-> ex a. LB(a,X))', 'DefBddBe');
def('ArchX', 'all a. all y. (y in ArchX(a) <-> y in Real & ex n. (n in Nat & y = iota(n) * a))', 'Def$X_a$');
def('negset', 'all X. all y. (y in negset(X) <-> y in Real & -y in X)', 'Def$\\ominus$');
def('Conv', 'all a. all al. (Conv(a,al) <-> Seq(a) & al in Real & all eps. (eps in Real -> 0 < eps -> ex N. (N in Nat & all n. (n in Nat -> N <= n -> abs(a[n] - al) < eps))))', 'DefConv');
def('Cgt', 'all a. (Cgt(a) <-> ex al. Conv(a,al))', 'DefCgt');
def('DvgP', 'all a. (DvgP(a) <-> Seq(a) & all K. (K in Real -> 0 < K -> ex N. (N in Nat & all n. (n in Nat -> N <= n -> K < a[n]))))', 'Def$\\mathrm{DvgP}$');
def('SeqBdd', 'all a. (SeqBdd(a) <-> Seq(a) & ex M. (M in Real & all n. (n in Nat -> abs(a[n]) <= M)))', 'DefSeqBdd');
def('MonoInc', 'all a. (MonoInc(a) <-> Seq(a) & all n. (n in Nat -> a[n] <= a[S(n)]))', 'DefMonoInc');
def('MonoDec', 'all a. (MonoDec(a) <-> Seq(a) & all n. (n in Nat -> a[S(n)] <= a[n]))', 'DefMonoDec');
def('Cauchy', 'all a. (Cauchy(a) <-> Seq(a) & all eps. (eps in Real -> 0 < eps -> ex N. (N in Nat & all m. all n. (m in Nat -> n in Nat -> N <= m -> N <= n -> abs(a[m] - a[n]) < eps))))', 'DefCauchy');
def('PNbhd', 'all f. all c. (PNbhd(f,c) <-> ex r. (r in Real & 0 < r & all x. (x in Real -> 0 < abs(x - c) -> abs(x - c) < r -> x in dom(f))))', 'DefPNbhd');
def('FLim', 'all f. all c. all al. (FLim(f,c,al) <-> RFn(f) & c in Real & al in Real & PNbhd(f,c) & all eps. (eps in Real -> 0 < eps -> ex de. (de in Real & 0 < de & all x. (x in dom(f) -> 0 < abs(x - c) -> abs(x - c) < de -> abs(f[x] - al) < eps))))', 'DefFLim');

module.exports = { registry, axiom, def, fthm, parse };
