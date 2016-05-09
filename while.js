const fs = require('fs');
const exec = require('child_process').exec;
const parsimmon = require('parsimmon');
const read = require('read-input');

const regex = parsimmon.regex;
const string = parsimmon.string;
const optWhitespace = parsimmon.optWhitespace;
const seq = parsimmon.seq;
const lazy = parsimmon.lazy;
const kw = (s) => string(s).skip(optWhitespace);

// datatype Type = NumT
//               | BoolT
// datatype Value = Num(nval: int)
//               | Bool(bval: bool)
// datatype Expr = V(val: Value)
//               | Var(name: string)
//               | Add(leftA: Expr, rightA: Expr)
//               | Eq(leftE: Expr, rightE: Expr)
// datatype Stmt = VarDecl(x: string, vtype: Type, vinit: Expr)
//               | If(cond: Expr, the: Stmt, els: Stmt)
//               | While(wcond: Expr, wbody: Stmt)
//               | Seq(Stmt, Stmt)
//               | Skip

const numTP = kw('Num').map(_ => "NumT");
const boolTP = kw('Bool').map(_ => "BoolT");
const typeP = numTP.or(boolTP);

const trueP = kw('true').map(_ => "Bool(true)");
const falseP = kw('false').map(_ => "Bool(false)");
const numP = regex(/0|[1-9][0-9]*/).skip(optWhitespace).map(s => `Num(${s})`);
const valP = trueP.or(falseP).or(numP).map(s => `V(${s})`);
const idP = regex(/[a-zA-Z_][a-zA-Z0-9_]*/).skip(optWhitespace);
const varP = idP.map(s => `Var("${s}")`);

const addP = lazy(() => seq(valP.or(varP).skip(kw('+')), addP).map(([a,b]) => `Add(${a},${b})`)
                       .or(valP.or(varP)));
const exprP = seq(addP.skip(kw('=')), addP).map(([a,b]) => `Eq(${a},${b})`)
             .or(addP);

const stmtP = lazy(() => {
  const blockP = kw('{').then(stmtP.many()).skip(kw('}')).map(s =>
    s.reduceRight((prev, stmt) => `Seq(${stmt}, ${prev})`, 'Skip'));
  const varDeclP = seq(kw('var').then(idP),
                       kw(':').then(typeP),
                       kw('=').then(exprP).skip(kw(';')))
                   .map(([x,t,init]) => `VarDecl("${x}",${t},${init})`);
  const ifP = seq(kw('if').then(kw('(')).then(exprP).skip(kw(')')),
                  kw('then').then(blockP),
                  kw('else').then(blockP))
              .map(([cond,the,els]) => `If(${cond},${the},${els})`);
  const whileP = seq(kw('while').then(kw('(')).then(exprP).skip(kw(')')),
                     blockP)
                 .map(([cond,body]) => `While(${cond},${body})`);
  return blockP.or(varDeclP).or(ifP).or(whileP);
});

const progP = stmtP.many().map(s =>
  s.reduceRight((prev, stmt) => `Seq(${stmt}, ${prev})`, 'Skip'));

read(process.argv.slice(2), function(err, res) {
  if (err) {
    console.error(err.message);
    process.exit(8);
  }
  const src = res.data.toString();
  console.log('Parsing...');
  const prog = progP.parse(src);
  if (!prog.status) {
    console.error(parsimmon.formatError(src, prog));
    process.exit(9);
  }
  const s = `include "./while.dfy"\nmethod Main() { Run(${prog.value}); }`;
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
