'use strict';
// =====================================================================
//  lang.js — 記号表とパーサ
//  論理式の入力記法:
//    all x. φ / ex x. φ / all x in A. φ / ex x in A. φ
//    ~φ, φ & ψ, φ | ψ, φ -> ψ, φ <-> ψ
//    t = u, t != u, t in u, t notin u, t sub u, t < u, t <= u, t > u, t >= u, P(t,...)
//    項: x, 0, 1, f(t,...), t + u, t * u, t - u, -t, t^-1, a[n] (列の第n項), abs(t)
// =====================================================================
const C = require('./core');
const { V, F, Eq, Rel, Not, Imp, All, And, Or, Iff, Ex, Le } = C;

// 記号表: 関数記号と関係記号
const funcs = new Map();   // name → { arity, tex: (args:string[]) => string, prec }
const preds = new Map();   // name → { arity, tex }
function defFunc(name, arity, tex, prec = 100) { funcs.set(name, { arity, tex, prec }); }
function defPred(name, arity, tex) { preds.set(name, { arity, tex }); }

// 組み込み
defPred('in', 2, a => `${a[0]} \\in ${a[1]}`);
defPred('<', 2, a => `${a[0]} < ${a[1]}`);
defPred('sub', 2, a => `${a[0]} \\subseteq ${a[1]}`);
defFunc('+', 2, a => `${a[0]} + ${a[1]}`, 10);
defFunc('*', 2, a => `${a[0]} \\cdot ${a[1]}`, 20);
defFunc('-', 2, a => `${a[0]} - ${a[1]}`, 10);
defFunc('neg', 1, a => `-${a[0]}`, 30);
defFunc('inv', 1, a => `${a[0]}^{-1}`, 40);
defFunc('app', 2, a => `${a[0]}(${a[1]})`, 100);
defFunc('abs', 1, a => `\\lvert ${a[0]} \\rvert`, 100);

// ---------- 字句解析 ----------
function tokenize(s) {
  const toks = []; let i = 0;
  const ops = ['<->', '->', '<=', '>=', '!=', '^-1', '=', '<', '>', '~', '&', '|', '(', ')', ',', '+', '*', '-', '[', ']', '.'];
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) { i++; continue; }
    if (/[A-Za-z_Ͱ-Ͽ]/.test(c)) {
      let j = i; while (j < s.length && /[A-Za-z0-9_'Ͱ-Ͽ]/.test(s[j])) j++;
      toks.push({ t: 'id', v: s.slice(i, j) }); i = j; continue;
    }
    if (/[0-9]/.test(c)) { let j = i; while (j < s.length && /[0-9]/.test(s[j])) j++; toks.push({ t: 'id', v: s.slice(i, j) }); i = j; continue; }
    const op = ops.find(o => s.startsWith(o, i));
    if (!op) throw new Error('tokenize: 不明な文字 ' + c + ' in ' + s);
    toks.push({ t: 'op', v: op }); i += op.length;
  }
  return toks;
}

// ---------- 構文解析 ----------
function parse(s, env = {}) {
  const toks = tokenize(s); let p = 0;
  const peek = () => toks[p], next = () => toks[p++];
  const isOp = v => peek() && peek().t === 'op' && peek().v === v;
  const isId = v => peek() && peek().t === 'id' && peek().v === v;
  const expect = v => { const t = next(); if (!t || t.v !== v) throw new Error(`parse: '${v}' が必要 (位置 ${p}) in ${s}`); };
  const fail = m => { throw new Error('parse: ' + m + ' in ' + s); };

  function formula() { return iff(); }
  function iff() { let a = imp(); while (isOp('<->')) { next(); a = Iff(a, imp()); } return a; }
  function imp() { const a = or(); if (isOp('->')) { next(); return Imp(a, imp()); } return a; }
  function or() { let a = and(); while (isOp('|')) { next(); a = Or(a, and()); } return a; }
  function and() { let a = unary(); while (isOp('&')) { next(); a = And(a, unary()); } return a; }
  function unary() {
    if (isOp('~')) { next(); return Not(unary()); }
    if (isId('all') || isId('ex')) {
      const q = next().v; const x = next().v;
      if (isId('in')) {
        next(); const A = term(); expect('.'); const body = formula();
        const m = Rel('in', V(x), A);
        return q === 'all' ? All(x, Imp(m, body)) : Ex(x, And(m, body));
      }
      expect('.'); const body = formula();
      return q === 'all' ? All(x, body) : Ex(x, body);
    }
    if (isOp('(')) { // 括弧付き論理式か, 項で始まる原子論理式か
      const save = p;
      try { next(); const f = formula(); expect(')'); if (peek() && peek().t === 'op' && ['=', '!=', '<', '<=', '>', '>=', '+', '*', '-', '^-1', '['].includes(peek().v)) throw 0; if (isId('in') || isId('notin') || isId('sub')) throw 0; return f; }
      catch (e) { p = save; }
    }
    return atom();
  }
  function atom() {
    if (isId('bot')) { next(); return Not(Eq(V('v0'), V('v0'))); }
    const t0 = peek();
    if (t0 && t0.t === 'id' && preds.has(t0.v) && !['in', '<', 'sub'].includes(t0.v)) {
      next(); expect('('); const args = []; if (!isOp(')')) { args.push(term()); while (isOp(',')) { next(); args.push(term()); } } expect(')');
      if (args.length !== preds.get(t0.v).arity) fail('arity of ' + t0.v);
      return Rel(t0.v, ...args);
    }
    const a = term(); const t = next();
    if (!t) fail('関係記号が必要');
    const b = () => term();
    switch (t.v) {
      case '=': return Eq(a, b());
      case '!=': return Not(Eq(a, b()));
      case '<': return Rel('<', a, b());
      case '<=': return Le(a, b());
      case '>': { const c = b(); return Rel('<', c, a); }
      case '>=': { const c = b(); return Le(c, a); }
      case 'in': return Rel('in', a, b());
      case 'notin': return Not(Rel('in', a, b()));
      case 'sub': return Rel('sub', a, b());
    }
    fail('不明な関係 ' + t.v);
  }
  function term() { return add(); }
  function add() {
    let a = mul();
    while (isOp('+') || isOp('-')) { const o = next().v; const b = mul(); a = o === '+' ? F('+', a, b) : F('-', a, b); }
    return a;
  }
  function mul() { let a = un(); while (isOp('*')) { next(); a = F('*', a, un()); } return a; }
  function un() { if (isOp('-')) { next(); return F('neg', un()); } return post(); }
  function post() {
    let a = prim();
    for (;;) {
      if (isOp('^-1')) { next(); a = F('inv', a); continue; }
      if (isOp('[')) { next(); const i = term(); expect(']'); a = F('app', a, i); continue; }
      break;
    }
    return a;
  }
  function prim() {
    const t = next();
    if (!t) fail('項が必要');
    if (t.t === 'op' && t.v === '(') { const a = term(); expect(')'); return a; }
    if (t.t !== 'id') fail('項が必要: ' + t.v);
    if (env[t.v]) return env[t.v];                       // メタ変数(既存の項を埋め込む)
    if (funcs.has(t.v)) {
      const fd = funcs.get(t.v);
      if (fd.arity === 0) return F(t.v);
      expect('('); const args = [term()]; while (isOp(',')) { next(); args.push(term()); } expect(')');
      if (args.length !== fd.arity) fail('arity of ' + t.v);
      return F(t.v, ...args);
    }
    return V(t.v);
  }
  const f = formula();
  if (p !== toks.length) fail('余分な字句 ' + JSON.stringify(toks.slice(p)));
  return f;
}
function parseTerm(s, env = {}) {
  const f = parse('(' + s + ') = (' + s + ')', env);
  return f.a;
}

module.exports = { funcs, preds, defFunc, defPred, parse, parseTerm };
