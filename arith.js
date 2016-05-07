const fs = require('fs');
const exec = require('child_process').exec;
const parsimmon = require('parsimmon');
const read = require('read-input');

const regex = parsimmon.regex;
const string = parsimmon.string;
const optWhitespace = parsimmon.optWhitespace;
const seq = parsimmon.seq;
const lazy = parsimmon.lazy;

// datatype Value = Num(n: int)
//               | Bool(b: bool)
// datatype Expr = V(Value)
//               | Add(leftA: Expr, rightA: Expr)
//               | Eq(leftE: Expr, rightE: Expr)
//               | If(cond: Expr, the: Expr, els: Expr)

const kw = (s) => string(s).skip(optWhitespace);

const trueP = kw('true').map(_ => "V(Bool(true))");
const falseP = kw('false').map(_ => "V(Bool(false))");
const numP = regex(/0|[1-9][0-9]*/).skip(optWhitespace).map(s => `V(Num(${s}))`);
const addP = lazy(() => seq(numP.skip(kw('+')), addP).map(([a,b]) => `Add(${a},${b})`)
                       .or(numP));
const eqP = seq(addP.skip(kw('=')), addP).map(([a,b]) => `Eq(${a},${b})`)
           .or(addP);
const exprP = lazy(() => seq(kw('if').then(eqP),
                             kw('then').then(exprP),
                             kw('else').then(exprP))
                        .map(([cond,the,els]) => `If(${cond},${the},${els})`)
                        .or(eqP));

read(process.argv.slice(2), function(err, res) {
  if (err) {
    console.error(err.message);
    process.exit(8);
  }
  const src = res.data.toString();
  console.log('Parsing...');
  const expr = exprP.parse(src);
  if (!expr.status) {
    console.error(parsimmon.formatError(src, expr));
    process.exit(9);
  }
  const s = `include "./arith.dfy"\nmethod Main() { Run(${expr.value}); }`;
  fs.writeFile('tmp.dfy', s, run);
});

function run(err) {
  if (err) {
    console.error(err.message);
    process.exit(10);
  }
  exec('dafny /nologo /compile:3 tmp.dfy', cleanup);
}

function cleanup(err, stdout, stderr) {
  console.log(stdout);
  console.error(stderr);
  fs.unlinkSync('tmp.dfy');
  if (err) {
    console.error(err.message);
    process.exit(12);
  }
}
// vim: sw=2
