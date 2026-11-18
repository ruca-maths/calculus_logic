'use strict';
// すべての証明スクリプトを実行し, 検証済みの証明木を ../gen/*.tex に書き出す
//   gen/<Name>.tex      : 完全展開した証明木 (\label{tree:<Name>})
//   gen/stmts.tex       : 各定理の形式的な主張 (\fsdef{Name}{ラベル}{論理式}{ノード数})
//   gen/part3.tex       : 第III部(証明木)の本体
//   gen/registry_*.tex  : 公理・定義公理・基礎定理の一覧
const fs = require('fs');
const path = require('path');
const K = require('./kit');
const { TX } = K;
const theory = require('./theory');

// 読み込み順(依存関係の順). 各スクリプトが証明する定理を記録する
const order = ['p_set', 'p_order', 'p_field', 'p_nat', 'p_abs', 'p_ch2', 'p_ch3', 'p_ch4', 'p_more', 'p_seq', 'p_seq2', 'p_seq3', 'p_seq4',
  'p_fun', 'p_cont', 'p_ivt', 'p_uc', 'p_geo', 'p_ser', 'p_inv', 'p_elem'];
const scripts = process.argv.slice(2).length ? process.argv.slice(2) : order;
const owner = new Map();  // script → [proved]
const header = new Map(); // script → 見出し
for (const s of scripts) {
  const file = path.join(__dirname, s + '.js');
  const before = K.proved.length;
  require('./' + s);
  owner.set(s, K.proved.slice(before));
  const m = fs.readFileSync(file, 'utf8').split('\n').find(l => l.startsWith('// ') && !l.startsWith('// ='));
  header.set(s, m ? m.slice(3).trim() : s);
}

const out = path.join(__dirname, '..', 'gen');
fs.mkdirSync(out, { recursive: true });
let total = 0;
const summary = [];
const nodesOf = new Map();
const esc = s => s.replace(/#/g, '\\#');
for (const p of K.proved) {
  const o = TX.emitProof(p.node, p.opt);
  const tex = `% 自動生成 (prover/build.js): ${p.name}  ノード数 ${o.stats.nodes}\n` +
    `\\begin{fullproof}{${p.label}}{$${TX.tex(p.f, true)}$}{${o.stats.nodes}}\\phantomsection\\label{tree:${p.name}}\n${o.tex}\\end{fullproof}\n`;
  fs.writeFileSync(path.join(out, p.name + '.tex'), tex);
  total += o.stats.nodes;
  nodesOf.set(p.name, o.stats.nodes);
  summary.push(`${p.name}\t${p.label}\t${o.stats.nodes}`);
}
// 形式的な主張
let st = '% 自動生成 (prover/build.js): 各定理の形式的な主張\n';
for (const p of K.proved) st += `\\fsdef{${p.name}}{${esc(p.label)}}{${TX.tex(p.f, true)}}{${nodesOf.get(p.name)}}\n`;
for (const r of theory.registry) if (r.kind !== 'Ax') st += `\\fsdef{${r.kind === 'F' ? 'F:' : 'D:'}${r.name}}{${esc(r.label ?? r.name)}}{${TX.tex(r.f, true)}}{0}\n`;
fs.writeFileSync(path.join(out, 'stmts.tex'), st);

// 第III部: テキストの章ごとにまとめる
const groups = [
  ['集合論と順序体', ['p_set', 'p_order', 'p_field', 'p_more', 'p_nat']],
  ['テキスト第1章 序論', ['p_abs']],
  ['テキスト第2章 実数の集合', ['p_ch2']],
  ['テキスト第3章 数列の極限', ['p_ch3', 'p_seq', 'p_seq2', 'p_geo', 'p_ser', 'p_seq3', 'p_seq4']],
  ['テキスト第4章 関数の極限', ['p_ch4', 'p_fun', 'p_cont', 'p_ivt', 'p_inv', 'p_elem', 'p_uc']],
];
let p3 = '% 自動生成 (prover/build.js): 第III部 証明木\n';
for (const [title, ss] of groups) {
  const present = ss.filter(s => owner.has(s) && owner.get(s).length);
  if (!present.length) continue;
  const n = present.reduce((a, s) => a + owner.get(s).reduce((b, p) => b + nodesOf.get(p.name), 0), 0);
  p3 += `\\chapter{${title} の証明木}\n本章の定理数 ${present.reduce((a, s) => a + owner.get(s).length, 0)}, ノード数の合計 ${n}.\n\n`;
  for (const s of present) {
    p3 += `\\section{${header.get(s).replace(/^テキスト/, '')}}\n`;
    for (const p of owner.get(s)) p3 += `\\input{gen/${p.name}}\n`;
  }
}
fs.writeFileSync(path.join(out, 'part3.tex'), p3);

// 公理・定義公理・基礎定理の一覧
for (const kind of ['Ax', 'Def', 'F']) {
  const items = theory.registry.filter(r => r.kind === kind);
  if (!items.length) continue;
  let reg = `\\begin{registrylist}\n`;
  for (const r of items) reg += `\\item[${r.label ?? r.name}] $${TX.tex(r.f, true)}$${r.note ? ` \\hfill{\\footnotesize(${r.note})}` : ''}\n`;
  reg += `\\end{registrylist}\n`;
  fs.writeFileSync(path.join(out, 'registry_' + kind + '.tex'), reg);
}
fs.writeFileSync(path.join(out, 'summary.txt'), summary.join('\n') + `\nTOTAL\t${total}\n`);
const nF = theory.registry.filter(r => r.kind === 'F').length, nD = theory.registry.filter(r => r.kind === 'Def').length;
fs.writeFileSync(path.join(out, 'stats.tex'), `\\newcommand{\\ThmCount}{${K.proved.length}}\\newcommand{\\NodeCount}{${total}}\\newcommand{\\FCount}{${nF}}\\newcommand{\\DefCount}{${nD}}\n`);
console.log('定理数', K.proved.length, '総ノード数', total);
