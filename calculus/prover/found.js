'use strict';
// 基礎定理 (status F): 本文で通常の証明を与えた ZFC の定理. 証明木の葉として用いる.
const { fthm } = require('./theory');

// ---- 完備順序体 (第5章 定理「R は完備順序体」, 第6章の表) ----
fthm('R1_0', '0 in Real', '(R1)');
fthm('R1_1', '1 in Real', '(R1)');
fthm('R1_add', 'all x. all y. (x in Real -> y in Real -> x + y in Real)', '(R1)');
fthm('R1_mul', 'all x. all y. (x in Real -> y in Real -> x * y in Real)', '(R1)');
fthm('R1_neg', 'all x. (x in Real -> -x in Real)', '(R1)');
fthm('R1_inv', 'all x. (x in Real -> x != 0 -> x^-1 in Real)', '(R1)');
fthm('R2', 'all x. all y. all z. (x in Real -> y in Real -> z in Real -> (x + y) + z = x + (y + z))', '(R2)');
fthm('R3', 'all x. all y. (x in Real -> y in Real -> x + y = y + x)', '(R3)');
fthm('R4', 'all x. (x in Real -> x + 0 = x)', '(R4)');
fthm('R5', 'all x. (x in Real -> x + -x = 0)', '(R5)');
fthm('R6', 'all x. all y. all z. (x in Real -> y in Real -> z in Real -> (x * y) * z = x * (y * z))', '(R6)');
fthm('R7', 'all x. all y. (x in Real -> y in Real -> x * y = y * x)', '(R7)');
fthm('R8', 'all x. (x in Real -> x * 1 = x)', '(R8)');
fthm('R8b', '0 != 1', '(R8)');
fthm('R9', 'all x. (x in Real -> x != 0 -> x * x^-1 = 1)', '(R9)');
fthm('R10', 'all x. all y. all z. (x in Real -> y in Real -> z in Real -> x * (y + z) = x * y + x * z)', '(R10)');
fthm('R13', 'all x. all y. (x in Real -> y in Real -> x < y | x = y | y < x)', '(R13)');
fthm('R14', 'all x. all y. all z. (x in Real -> y in Real -> z in Real -> x < y -> x + z < y + z)', '(R14)');
fthm('R15', 'all x. all y. (x in Real -> y in Real -> 0 < x -> 0 < y -> 0 < x * y)', '(R15)');
fthm('R16', 'all X. (X sub Real -> X != emptyset -> (ex b. UB(b,X)) -> ex s. IsSup(s,X))', '(R16)');

// ---- 自然数と埋め込み ι (第4章, 第6章) ----
fthm('NatCup', 'all m. all n. (m in Nat -> n in Nat -> cup(m,n) in Nat)', '[N3]', '補題(最大値)');
fthm('IotaR', 'all n. (n in Nat -> iota(n) in Real)', '[N4]', '補題(ι)');
fthm('Iota1', 'iota(onew) = 1', '[N5]', '補題(ι)');
fthm('IotaS', 'all n. (n in Nat -> iota(S(n)) = iota(n) + 1)', '[N6]', '補題(ι)');

// ---- 数列 (第3章の関数の基本性質と定義 (x∈A↦t) から) ----
fthm('SeqVal', 'all a. all n. (Seq(a) -> n in Nat -> a[n] in Real)', '[S1]', '補題(関数値)');
fthm('Oplus', 'all a. all b. (Seq(a) -> Seq(b) -> Seq(oplus(a,b)) & all n. (n in Nat -> oplus(a,b)[n] = a[n] + b[n]))', '[S2]', '定義 (x∈A↦t)');
fthm('Odot', 'all c. all a. (c in Real -> Seq(a) -> Seq(odot(c,a)) & all n. (n in Nat -> odot(c,a)[n] = c * a[n]))', '[S3]', '定義 (x∈A↦t)');
fthm('Otimes', 'all a. all b. (Seq(a) -> Seq(b) -> Seq(otimes(a,b)) & all n. (n in Nat -> otimes(a,b)[n] = a[n] * b[n]))', '[S4]', '定義 (x∈A↦t)');
fthm('Recip', 'all a. (Seq(a) -> (all n. (n in Nat -> a[n] != 0)) -> Seq(recip(a)) & all n. (n in Nat -> recip(a)[n] = a[n]^-1))', '[S5]', '定義 (x∈A↦t)');
fthm('RFnVal', 'all f. all x. (RFn(f) -> x in dom(f) -> f[x] in Real)', '[S6]', '補題(関数値)');
fthm('RFnDom', 'all f. all x. (RFn(f) -> x in dom(f) -> x in Real)', '[S7]', '補題(関数値)');

// ---- 関数の合成 (第3章 定義 (x∈A↦t) から) ----
require('./lang').defFunc('compseq', 2, a => `${a[0]} \\circ ${a[1]}`, 50);
require('./lang').defFunc('comp', 2, a => `${a[0]} \\circ ${a[1]}`, 50);
fthm('CompSeq', 'all f. all a. (RFn(f) -> Seq(a) -> (all n. (n in Nat -> a[n] in dom(f))) -> Seq(compseq(f,a)) & all n. (n in Nat -> compseq(f,a)[n] = f[a[n]]))', '[S8]', '定義 (x∈A↦t)');
fthm('CompFn', 'all g. all f. (RFn(g) -> RFn(f) -> RFn(comp(g,f)) & all x. (x in dom(comp(g,f)) -> x in dom(f) & f[x] in dom(g) & comp(g,f)[x] = g[f[x]]))', '[S9]', '定義 (x∈A↦t)');
