datatype Option<T> = None | Some(val: T)

datatype Type = NumT
              | BoolT
              | RefT(t: Type)
datatype Value = Num(nval: int)
              | Bool(bval: bool)
              | Ref(l: nat, t: Type)
datatype Expr = V(val: Value)
              | Var(name: string)
              | Add(leftA: Expr, rightA: Expr)
              | Eq(leftE: Expr, rightE: Expr)
              | GT(leftG: Expr, rightG: Expr)
datatype Stmt = VarDecl(x: string, vtype: Type, vinit: Expr)
              | Assign(y: string, expr: Expr)
              | If(cond: Expr, the: Stmt, els: Stmt)
              | CleanUp(g: Gamma, refs: Stmt, decls: Stmt)
              | While(wcond: Expr, wbody: Stmt)
              | Seq(s1: Stmt, s2: Stmt)
              | Skip

// --------- Parsing ---------

function method SatP(f: char -> bool, s: string): Option<(char, string)>
reads f.reads;
requires forall c :: f.requires(c);
ensures SatP(f, s).Some? ==> |SatP(f, s).val.1| < |s|;
{
  if |s| > 0 && f(s[0]) then
    Some((s[0], s[1..]))
  else
    None
}

function method Ch(c: char, s: string): Option<(char, string)>
ensures Ch(c, s).Some? ==> |Ch(c, s).val.1| < |s|;
{
  SatP(c1 => c == c1, s)
}

function method KW(kw: string, s: string): Option<(string,string)>
ensures KW(kw, s).Some? && |kw| >= 1 ==> |KW(kw, s).val.1| < |s|;
{
  if |kw| == 0 then (
    Some(("", s))
  ) else (
    var t := Ch(kw[0], s);
    if t.None? then None else (
      var r := KW(kw[1..], t.val.1);
      if r.None? then None else Some(([kw[0]] + r.val.0, r.val.1))
    )
  )
}

function method Map<A,B>(i: Option<(A, string)>, f: A -> B):  Option<(B, string)>
reads f.reads;
requires forall a :: f.requires(a);
ensures Map(i, f).Some? <==> i.Some?;
ensures Map(i, f).Some? ==> |Map(i, f).val.1| == |i.val.1|;
{
  if i.Some? then Some((f(i.val.0), i.val.1)) else None
}

function method Or<A>(a: Option<(A, string)>, b: Option<(A, string)>):  Option<(A, string)>
ensures Or(a, b).Some? ==> a.Some? || b.Some?;
ensures Or(a, b).Some? && a.Some? ==> |Or(a, b).val.1| == |a.val.1|;
ensures Or(a, b).Some? && !a.Some? ==> |Or(a, b).val.1| == |b.val.1|;
{
  if a.Some? then a else b
}

function method ParseNumT(s: string): Option<(Type, string)>
ensures ParseNumT(s).Some? ==> |ParseNumT(s).val.1| < |s|;
{
  Map(KW("Num", s), (_) => NumT)
}

function method ParseBoolT(s: string): Option<(Type, string)>
ensures ParseBoolT(s).Some? ==> |ParseBoolT(s).val.1| < |s|;
{
  Map(KW("Bool", s), (_) => BoolT)
}

function method ParseType(s: string): Option<(Type, string)>
ensures ParseType(s).Some? ==> |ParseType(s).val.1| < |s|;
{
  Or(ParseBoolT(s), ParseNumT(s))
}

function method ParseTrue(s: string): Option<(Value, string)>
ensures ParseTrue(s).Some? ==> |ParseTrue(s).val.1| < |s|;
{
  Map(KW("true", s), (_) => Bool(true))
}

function method ParseFalse(s: string): Option<(Value, string)>
ensures ParseFalse(s).Some? ==> |ParseFalse(s).val.1| < |s|;
{
  Map(KW("false", s), (_) => Bool(false))
}

function method ParseDigit(s: string): Option<(int, string)>
ensures ParseDigit(s).Some? ==> |ParseDigit(s).val.1| < |s|;
{
  Or(Or(Or(Or(Or(Or(Or(Or(Or(Map(Ch('0', s), c => 0),
                             Map(Ch('1', s), c => 1)),
                          Map(Ch('2', s), c => 2)),
                       Map(Ch('3', s), c => 3)),
                    Map(Ch('4', s), c => 4)),
                 Map(Ch('5', s), c => 5)),
              Map(Ch('6', s), c => 6)),
           Map(Ch('7', s), c => 7)),
        Map(Ch('8', s), c => 8)),
     Map(Ch('9', s), c => 9))
}

function method ParseNumRec(s: string, i: nat, n: int): (int, string)
decreases n;
requires n >= 0;
ensures |ParseNumRec(s, i, n).1| <= |s|;
{
  if n == 0 then (
    (i, s)
  ) else (
    var t := ParseDigit(s);
    if t.None? then (i, s) else ParseNumRec(t.val.1, i * 10 + t.val.0, n - 1)
  )
}

function method ParseNum(s: string): Option<(Value, string)>
ensures ParseNum(s).Some? ==> |ParseNum(s).val.1| < |s|;
{
  var t := ParseDigit(s);
  if t.None? then None else Map(Some(ParseNumRec(t.val.1, t.val.0, 10)), n => Num(n))
}

function method ParseVal(s: string): Option<(Expr, string)>
ensures ParseVal(s).Some? ==> |ParseVal(s).val.1| < |s|;
{
  Map(Or(Or(ParseTrue(s),
            ParseFalse(s)),
         ParseNum(s)), v => V(v))
}

function method ParseIdRec(s: string, n: nat): (string, string)
decreases n;
ensures |ParseIdRec(s, n).1| <= |s|;
{
  if n == 0 then (
    ("", s)
  ) else (
    var t := SatP(c => 'A' <= c <= 'Z' || 'a' <= c <= 'z' || c == '_' || '0' <= c <= '9', s);
    if t.None? then
      ("", s)
    else (
      var r := ParseIdRec(t.val.1, n - 1);
      ([t.val.0] + r.0, r.1)
    )
  )
}

function method ParseId(s: string): Option<(string, string)>
ensures ParseId(s).Some? ==> |ParseId(s).val.1| < |s|;
{
  var t := SatP(c => 'A' <= c <= 'Z' || 'a' <= c <= 'z' || c == '_', s);
  if t.None? then None else (
    var r := ParseIdRec(t.val.1, 10);
    Some(([t.val.0] + r.0, r.1))
  )
}

function method ParseVar(s: string): Option<(Expr, string)>
ensures ParseVar(s).Some? ==> |ParseVar(s).val.1| < |s|;
{
  Map(ParseId(s), s => Var(s))
}

function method SkipWS<A>(s: Option<(A,string)>): Option<(A,string)>
decreases if s.Some? then |s.val.1| else 0;
ensures s.Some? <==> SkipWS(s).Some?;
ensures SkipWS(s).Some? ==> |SkipWS(s).val.1| <= |s.val.1|;
{
  if s.Some? && |s.val.1| > 0 && (s.val.1[0] == ' ' || s.val.1[0] == '\n' || s.val.1[0] == '\t') then
    SkipWS(Some((s.val.0, s.val.1[1..])))
  else
    s
}

function method ParseAddRec(s: string, n: nat): Option<(Expr, string)>
decreases n;
ensures ParseAddRec(s, n).Some? ==> |ParseAddRec(s, n).val.1| < |s|;
{
  var t := SkipWS(Or(ParseVal(s), ParseVar(s)));
  if n == 0 || t.None? then t else (
    var p := SkipWS(Ch('+', t.val.1));
    if p.None? then t else (
      var r := ParseAddRec(p.val.1, n - 1);
      if r.None? then t else Some((Add(t.val.0, r.val.0), r.val.1))
    )
  )
}

function method ParseAdd(s: string): Option<(Expr, string)>
ensures ParseAdd(s).Some? ==> |ParseAdd(s).val.1| < |s|;
{
  ParseAddRec(s, 100)
}

function method ParseExprRec(s: string, n: nat): Option<(Expr, string)>
decreases n;
ensures ParseExprRec(s, n).Some? ==> |ParseExprRec(s, n).val.1| < |s|;
{
  var t := ParseAdd(s);
  if n == 0 || t.None? then t else (
    var p := SkipWS(Or(KW(">", t.val.1), KW("==", t.val.1)));
    if p.None? then t else (
      var r := ParseExprRec(p.val.1, n - 1);
      if r.None? then t else Some((
        if p.val.0 == ">" then GT(t.val.0, r.val.0) else Eq(t.val.0, r.val.0),
        r.val.1))
    )
  )
}

function method ParseExpr(s: string): Option<(Expr, string)>
ensures ParseExpr(s).Some? ==> |ParseExpr(s).val.1| < |s|;
{
  ParseExprRec(s, 100)
}

function method ParseBlock(s: string, n: nat): Option<(Stmt, string)>
decreases |s|, n;
ensures ParseBlock(s, n).Some? ==> |ParseBlock(s, n).val.1| < |s|;
{
  var l := SkipWS(Ch('{', s));
  if l.None? then None else (
    assert |l.val.1| < |s|;
    var stmts := ParseProgRec(l.val.1, n);
    if stmts.None? then (
      var r := SkipWS(Ch('}', l.val.1));
      if r.None? then None else Some((Skip, r.val.1))
    ) else (
      var r := SkipWS(Ch('}', stmts.val.1));
      if r.None? then None else Some((stmts.val.0, r.val.1))
    )
  )
}

function method ParseVarDecl(s: string): Option<(Stmt, string)>
ensures ParseVarDecl(s).Some? ==> |ParseVarDecl(s).val.1| < |s|;
{
  var v := SkipWS(KW("var", s));
  if v.None? then None else (
    var id := SkipWS(ParseId(v.val.1));
    if id.None? then None else (
      var c := SkipWS(Ch(':', id.val.1));
      if c.None? then None else (
        var t := SkipWS(ParseType(c.val.1));
        if t.None? then None else (
          var e := SkipWS(Ch('=', t.val.1));
          if e.None? then None else (
            var i := ParseExpr(e.val.1);
            if i.None? then None else (
              var s := SkipWS(Ch(';', i.val.1));
              if s.None? then None else Some((VarDecl(id.val.0, t.val.0, i.val.0), s.val.1))))))))
}

function method ParseAssign(s: string): Option<(Stmt, string)>
ensures ParseAssign(s).Some? ==> |ParseAssign(s).val.1| < |s|;
{
  var id := SkipWS(ParseId(s));
  if id.None? then None else (
    var e := SkipWS(Ch('=', id.val.1));
    if e.None? then None else (
      var i := ParseExpr(e.val.1);
      if i.None? then None else (
        var s := SkipWS(Ch(';', i.val.1));
        if s.None? then None else Some((Assign(id.val.0, i.val.0), s.val.1)))))
}

function method ParseIf(s: string, n: nat): Option<(Stmt, string)>
decreases |s|, n;
ensures ParseIf(s, n).Some? ==> |ParseIf(s, n).val.1| < |s|;
{
  var ifk := SkipWS(KW("if", s));
  if ifk.None? then None else (
    var lc := SkipWS(Ch('(', ifk.val.1));
    if lc.None? then None else (
      var con := ParseExpr(lc.val.1);
      if con.None? then None else (
        var rc := SkipWS(Ch(')', con.val.1));
        if rc.None? then None else (
          var the := ParseBlock(rc.val.1, n);
          if the.None? then None else (
            var elskw := SkipWS(KW("else", the.val.1));
            if elskw.None? then (
              Some((If(con.val.0, the.val.0, Skip), the.val.1))
            ) else (
              var els := ParseBlock(elskw.val.1, n);
              if els.None? then None else Some((If(con.val.0, the.val.0, els.val.0), els.val.1))))))))
}

function method ParseWhile(s: string, n: nat): Option<(Stmt, string)>
decreases |s|, n;
ensures ParseWhile(s, n).Some? ==> |ParseWhile(s, n).val.1| < |s|;
{
  var wk := SkipWS(KW("while", s));
  if wk.None? then None else (
    var lc := SkipWS(Ch('(', wk.val.1));
    if lc.None? then None else (
      var con := ParseExpr(lc.val.1);
      if con.None? then None else (
        var rc := SkipWS(Ch(')', con.val.1));
        if rc.None? then None else (
          var body := ParseBlock(rc.val.1, n);
          if body.None? then None else Some((While(con.val.0, body.val.0), body.val.1))))))
}

function method ParseProgRec(s: string, n: nat): Option<(Stmt, string)>
decreases |s|, n;
ensures ParseProgRec(s, n).Some? ==> |ParseProgRec(s, n).val.1| < |s|;
{
  if n == 0 then None else (
    var s1 := Or(Or(Or(ParseVarDecl(s),
                       ParseIf(s, n - 1)),
                    ParseWhile(s, n - 1)),
                 ParseAssign(s));
    if s1.None? then None else (
      var s2 := ParseProgRec(s1.val.1, n - 1);
      if s2.None? then s1 else Some((Seq(s1.val.0, s2.val.0), s2.val.1))
    )
  )
}

class FileSystem {
  extern static method ReadCmdLine() returns (contents: array<char>)
}

method Parse() returns (res: Option<Stmt>) {
  var contents: array<char> := FileSystem.ReadCmdLine();
  if contents == null { return None; }
  var pres := SkipWS(ParseProgRec(contents[..], 10000));
  if pres.None? || |pres.val.1| > 0 { return None; }
  res := Some(pres.val.0);
}

// --------- Type Checking ---------

type Gamma = map<string, Type>

function method GammaJoin(g1: Gamma, g2: Gamma): Gamma
ensures GammaExtends(GammaJoin(g1, g2), g1);
ensures GammaExtends(GammaJoin(g1, g2), g2);
{
  map x | x in g1 && x in g2 && g1[x] == g2[x] :: g1[x]
}

function method GammaUnion(g1: Gamma, g2: Gamma): Gamma
ensures GammaExtends(g2, GammaUnion(g1, g2));
ensures forall x :: x in GammaUnion(g1, g2) ==> x in g1 || x in g2;
{
  var g1k: set<string> := (set x | x in g1);
  var g2k: set<string> := (set x | x in g2);
  map x | x in g1k + g2k :: if x in g2k then g2[x] else g1[x]
}

predicate GammaExtends(gamma1: Gamma, gamma2: Gamma)
ensures GammaExtends(gamma1, gamma2) ==> forall x :: x in gamma1 ==> x in gamma2;
{
  forall x :: x in gamma1 ==> x in gamma2 && gamma1[x] == gamma2[x]
}

predicate method MoveType(t: Type) {
  t.RefT?
}

predicate GammaDeclarationsE(g: Gamma, expr: Expr) {
  forall x :: x in ReferencedVarsE(expr) ==> x in g
}

predicate GammaDeclarationsS(g: Gamma, stmt: Stmt)
{
  forall x :: x in ReferencedVarsS(stmt) ==> x in g
}

function method DeclaredVars(stmt: Stmt): Gamma
decreases stmt;
{
  match stmt {
    case VarDecl(x, vtype, vinit) => map[x := vtype]
    case Assign(y, expr) => map[]
    case If(con, the, els) => GammaUnion(DeclaredVars(the), DeclaredVars(els))
    case CleanUp(g, refs, decls) => map[]
    case While(con, body) => map[]
    case Seq(s1, s2) => GammaUnion(DeclaredVars(s1), DeclaredVars(s2))
    case Skip => map[]
  }
}

function method ScopedVars(stmt: Stmt): Gamma
decreases stmt;
ensures forall x :: x in ScopedVars(stmt) ==> x in DeclaredVars(stmt);
{
  match stmt {
    case VarDecl(x, vtype, vinit) => map[x := vtype]
    case Assign(y, expr) => map[]
    case If(con, the, els) => map[]
    case CleanUp(g, refs, decls) => map[]
    case While(con, body) => map[]
    case Seq(s1, s2) => GammaUnion(GammaWithoutMovedS(ScopedVars(s1), s2), ScopedVars(s2))
    case Skip => map[]
  }
}

function method ReferencedVarsE(expr: Expr): set<string>
{
  match expr {
    case V(val) => {}
    case Var(x) => {x}
    case Add(l, r) => ReferencedVarsE(l) + ReferencedVarsE(r)
    case GT(l, r) => ReferencedVarsE(l) + ReferencedVarsE(r)
    case Eq(l, r) => ReferencedVarsE(l) + ReferencedVarsE(r)
  }
}

function method ReferencedVarsS(stmt: Stmt): set<string>
decreases stmt;
{
  ReferencedVarsSDec(stmt, 0)
}

function method ReferencedVarsSDec(stmt: Stmt, n: nat): set<string>
decreases stmt, n;
{
  match stmt {
    case VarDecl(x, vtype, vinit) =>
      ReferencedVarsE(vinit)
    case Assign(y, expr) => ReferencedVarsE(expr) - {y}
    case If(con, the, els) =>
      ReferencedVarsE(con) + ReferencedVarsS(the) + ReferencedVarsS(els)
    case CleanUp(g, refs, decls) => {}
    case While(con, body) =>
      ReferencedVarsE(con) + ReferencedVarsS(body)
    case Seq(s1, s2) =>
      ReferencedVarsS(s1) +
      (set x | x in ReferencedVarsS(s2) && x !in ScopedVars(s1) :: x)
    case Skip => {}
  }
}

predicate ConsumedVarsSInv(stmt: Stmt, n: nat, n2: nat)
ensures ConsumedVarsS(stmt, n) == ConsumedVarsS(stmt, n2);
{
  var res := ConsumedVarsS(stmt, n);
  var res2 := ConsumedVarsS(stmt, n2);
  match stmt {
    case VarDecl(x, vtype, vinit) => (
      assert res == res2;
      true
    )
    case Assign(y, expr) => (
      assert res == res2;
      true
    )
    case If(con, the, els) => (
      assert res == res2;
      true
    )
    case CleanUp(g, refs, decls) => (
      assert res == res2;
      true
    )
    case While(con, body) => (
      assert res == res2;
      true
    )
    case Seq(s1, s2) => (
      assert res == res2;
      true
    )
    case Skip => (
      assert res == res2;
      true
    )
  }
}

lemma ConsumedVarsSInvA(stmt: Stmt)
ensures forall i:nat , j:nat :: ConsumedVarsS(stmt, i) == ConsumedVarsS(stmt, j);
{
  assert forall i:nat, j:nat :: ConsumedVarsSInv(stmt, i, j);
}

function method ConsumedVarsS(stmt: Stmt, n: nat): set<string>
decreases stmt, n;
{
  match stmt {
    case VarDecl(x, vtype, vinit) => {}
    case Assign(y, expr) => {}
    case If(con, the, els) => ConsumedVarsS(the, 1) + ConsumedVarsS(els, 1)
    case CleanUp(g, refs, decls) =>
      (set x | x in ScopedVars(decls)) + (set x | x in ReferencedVarsS(refs) && x in g && MoveType(g[x]))
                                       + ConsumedVarsS(refs, 1)
    case While(con, body) => ConsumedVarsS(body, 1)
    case Seq(s1, s2) => ConsumedVarsS(s1, 1) + ConsumedVarsS(s2, 1)
    case Skip => {}
  }
}

function GammaWithoutMovedE(g: Gamma, expr: Expr): Gamma
ensures GammaExtends(GammaWithoutMovedE(g, expr), g);
{
  map x | x in g && (x !in ReferencedVarsE(expr) || !MoveType(g[x])) :: g[x]
}

function method GammaWithoutMovedS(g: Gamma, stmt: Stmt): Gamma
ensures GammaExtends(GammaWithoutMovedS(g, stmt), g);
decreases stmt;
{
  map x | x in g && !(x in ReferencedVarsSDec(stmt, 0) && MoveType(g[x]))
                 && !(x in ConsumedVarsS(stmt, 0)):: g[x]
}

predicate GammaWithoutMovedSeqDistributionStr1(g: Gamma, s1: Stmt, s2: Stmt, x: string)
requires x in GammaWithoutMovedS(GammaWithoutMovedS(g, s1), s2);
ensures x in GammaWithoutMovedS(g, Seq(s1,s2));
{
  assert x in g;
  assert x !in ConsumedVarsS(s1, 0);
  assert x !in ConsumedVarsS(s2, 0);
  assert x !in ConsumedVarsS(Seq(s1, s2), 0);

  if MoveType(g[x]) then (
    assert x !in ReferencedVarsSDec(s1, 0);
    assert x !in ReferencedVarsSDec(s2, 0);
    assert x !in (set y | y in ReferencedVarsS(s2) && y !in ScopedVars(s1) :: y);
    assert x !in ReferencedVarsSDec(Seq(s1, s2), 0);
    assert x in GammaWithoutMovedS(g, Seq(s1,s2));
    true
  ) else (
    assert x in GammaWithoutMovedS(g, Seq(s1,s2));
    true
  )
}

predicate GammaWithoutMovedSeqDistributionStr2(g: Gamma, s1: Stmt, s2: Stmt, x: string)
requires g !! ScopedVars(s1);
requires x in GammaWithoutMovedS(g, Seq(s1,s2));
ensures x in GammaWithoutMovedS(GammaWithoutMovedS(g, s1), s2);
{
  assert x in g;
  assert x !in ConsumedVarsS(Seq(s1, s2), 0);
  assert x !in ConsumedVarsS(s1, 1) + ConsumedVarsS(s2, 1);
  assert x !in ConsumedVarsS(s1, 0) + ConsumedVarsS(s2, 0);
  assert x !in ConsumedVarsS(s1, 0);
  assert x !in ConsumedVarsS(s2, 0);

  if MoveType(g[x]) then (
    assert x !in ReferencedVarsSDec(Seq(s1, s2), 0);
    assert x !in ReferencedVarsS(s1) + (set x | x in ReferencedVarsS(s2) && x !in ScopedVars(s1) :: x);

    assert x !in ReferencedVarsS(s1);
    assert x in GammaWithoutMovedS(g, s1);
    assert x !in ReferencedVarsS(s2) || x in ScopedVars(s1);
    assert x !in ScopedVars(s1);
    assert x !in ReferencedVarsS(s2);
    assert x in GammaWithoutMovedS(GammaWithoutMovedS(g, s1), s2);
    true
  ) else (
    assert x in GammaWithoutMovedS(GammaWithoutMovedS(g, s1), s2);
    true
  )
}

lemma GammaWithoutMovedSeqDistribution(g: Gamma, s1: Stmt, s2: Stmt)
requires g !! ScopedVars(s1);
ensures GammaWithoutMovedS(g, Seq(s1,s2)) == GammaWithoutMovedS(GammaWithoutMovedS(g, s1), s2);
{
  assert forall x :: x in GammaWithoutMovedS(GammaWithoutMovedS(g, s1), s2)
                 ==> GammaWithoutMovedSeqDistributionStr1(g, s1, s2, x)
                 ==> x in GammaWithoutMovedS(g, Seq(s1,s2));
  assert forall x :: x in GammaWithoutMovedS(g, Seq(s1,s2))
                 ==> GammaWithoutMovedSeqDistributionStr2(g, s1, s2, x)
                 ==> x in GammaWithoutMovedS(GammaWithoutMovedS(g, s1), s2);
}

predicate GammaWithoutMovedWhileDistributionStr1(g: Gamma, con: Expr, body: Stmt, x: string)
requires x in GammaJoin(GammaWithoutMovedE(g, con), GammaWithoutMovedS(GammaWithoutMovedE(g, con), body));
ensures x in GammaWithoutMovedS(g, While(con, body));
{
  assert x in GammaWithoutMovedE(g, con);
  assert x in g;
  assert x !in ConsumedVarsS(body, 0);
  assert x !in ConsumedVarsS(While(con, body), 0);
  if MoveType(g[x]) then (
    assert x !in ReferencedVarsE(con);
    assert x !in ReferencedVarsS(body);
    assert x in GammaWithoutMovedS(g, While(con, body));
    true
  ) else (
    assert x in GammaWithoutMovedS(g, While(con, body));
    true
  )
}

predicate GammaWithoutMovedWhileDistributionStr2(g: Gamma, con: Expr, body: Stmt, x: string)
requires x in GammaWithoutMovedS(g, While(con, body));
ensures x in GammaJoin(GammaWithoutMovedE(g, con), GammaWithoutMovedS(GammaWithoutMovedE(g, con), body));
{
  assert x in g;
  assert x !in ConsumedVarsS(While(con, body), 0);
  assert x !in ConsumedVarsS(body, 1);
  assert x !in ConsumedVarsS(body, 0);
  if MoveType(g[x]) then (
    assert x !in ReferencedVarsS(While(con, body));
    assert x !in ReferencedVarsSDec(While(con, body), 0);
    assert x !in ReferencedVarsE(con) + ReferencedVarsS(body);
    assert x !in ReferencedVarsE(con);
    assert x !in ReferencedVarsS(body);
    assert x in GammaWithoutMovedE(g, con);
    assert x in GammaWithoutMovedS(GammaWithoutMovedE(g, con), body);
    assert x in GammaJoin(GammaWithoutMovedE(g, con), GammaWithoutMovedS(GammaWithoutMovedE(g, con), body));
    true
  ) else (
    assert x in GammaJoin(GammaWithoutMovedE(g, con), GammaWithoutMovedS(GammaWithoutMovedE(g, con), body));
    true
  )
}

lemma GammaWithoutMovedWhileDistribution(g: Gamma, con: Expr, body: Stmt)
ensures GammaJoin(GammaWithoutMovedE(g, con), GammaWithoutMovedS(GammaWithoutMovedE(g, con), body))
     == GammaWithoutMovedS(g, While(con, body));
{
  assert forall x :: x in GammaJoin(GammaWithoutMovedE(g, con), GammaWithoutMovedS(GammaWithoutMovedE(g, con), body))
                 ==> GammaWithoutMovedWhileDistributionStr1(g, con, body, x)
                 ==> x in GammaWithoutMovedS(g, While(con, body));
  assert forall x :: x in GammaWithoutMovedS(g, While(con, body))
                 ==> GammaWithoutMovedWhileDistributionStr2(g, con, body, x)
                 ==> x in GammaJoin(GammaWithoutMovedE(g, con), GammaWithoutMovedS(GammaWithoutMovedE(g, con), body));
}

predicate GammaWithoutMovedIfDistributionStr1(g: Gamma, cond: Expr, the: Stmt, els: Stmt, x: string)
requires x in GammaWithoutMovedS(GammaWithoutMovedS(GammaWithoutMovedE(g, cond), the), els);
ensures x in GammaWithoutMovedS(g, If(cond, the, els));
{
  assert x in g;
  assert x !in ConsumedVarsS(the, 0);
  assert x !in ConsumedVarsS(els, 0);
  assert x !in ConsumedVarsS(If(cond, the, els), 0);
  if MoveType(g[x]) then (
    assert x !in ReferencedVarsE(cond);
    assert x !in ReferencedVarsS(the);
    assert x !in ReferencedVarsS(els);
    assert x !in ReferencedVarsS(If(cond, the, els));
    assert x in GammaWithoutMovedS(g, If(cond, the, els));
    true
  ) else (
    assert x in GammaWithoutMovedS(g, If(cond, the, els));
    true
  )
}

predicate GammaWithoutMovedIfDistributionStr2(g: Gamma, cond: Expr, the: Stmt, els: Stmt, x: string)
requires x in GammaWithoutMovedS(g, If(cond, the, els));
ensures x in GammaWithoutMovedS(GammaWithoutMovedS(GammaWithoutMovedE(g, cond), the), els);
{
  assert x in g;
  assert x !in ConsumedVarsS(If(cond, the, els), 0);
  assert x !in ConsumedVarsS(the, 1) + ConsumedVarsS(els, 1);
  assert x !in ConsumedVarsS(the, 0) + ConsumedVarsS(els, 0);
  assert x !in ConsumedVarsS(the, 0);
  assert x !in ConsumedVarsS(els, 0);
  if MoveType(g[x]) then (
    assert x !in ReferencedVarsS(If(cond, the, els));
    assert x !in ReferencedVarsSDec(If(cond, the, els), 0);
    assert x !in ReferencedVarsE(cond) + ReferencedVarsS(the) + ReferencedVarsS(els);
    assert x !in ReferencedVarsE(cond);
    assert x !in ReferencedVarsS(the);
    assert x !in ReferencedVarsS(els);
    assert x in GammaWithoutMovedS(GammaWithoutMovedS(GammaWithoutMovedE(g, cond), the), els);
    true
  ) else (
    assert x in GammaWithoutMovedS(GammaWithoutMovedS(GammaWithoutMovedE(g, cond), the), els);
    true
  )
}

lemma GammaWithoutMovedIfDistribution(g: Gamma, cond: Expr, the: Stmt, els: Stmt)
ensures GammaWithoutMovedS(g, If(cond, the, els)) ==
        GammaWithoutMovedS(GammaWithoutMovedS(GammaWithoutMovedE(g, cond), the), els);
{
  assert forall x :: x in GammaWithoutMovedS(GammaWithoutMovedS(GammaWithoutMovedE(g, cond), the), els)
                 ==> GammaWithoutMovedIfDistributionStr1(g, cond, the, els, x)
                 ==> x in GammaWithoutMovedS(g, If(cond, the, els));
  assert forall x :: x in GammaWithoutMovedS(g, If(cond, the, els))
                 ==> GammaWithoutMovedIfDistributionStr2(g, cond, the, els, x)
                 ==> x in GammaWithoutMovedS(GammaWithoutMovedS(GammaWithoutMovedE(g, cond), the), els);
}

datatype TypeCheckERes = Fail | Type(gamma: Gamma, typ: Type)
function method TypeCheckV(val: Value): Type
{
  match val {
    case Num(_) => NumT
    case Bool(_) => BoolT
    case Ref(_, t) => RefT(t)
  }
}

function method TypeCheckE(g: Gamma, expr: Expr): TypeCheckERes
decreases expr;
ensures TypeCheckE(g, expr).Type? ==>
        GammaDeclarationsE(g, expr);
ensures TypeCheckE(g, expr).Type? ==>
        TypeCheckE(g, expr).gamma == GammaWithoutMovedE(g, expr);
ensures TypeCheckE(g, expr).Type? && expr.Add? ==>
        TypeCheckE(g, expr).typ.NumT? &&
        TypeCheckE(g, expr.leftA).Type? &&
        TypeCheckE(g, expr.leftA).typ.NumT? &&
        TypeCheckE(GammaWithoutMovedE(g, expr.leftA), expr.rightA).Type? &&
        TypeCheckE(GammaWithoutMovedE(g, expr.leftA), expr.rightA).typ.NumT?;
ensures TypeCheckE(g, expr).Type? && expr.GT? ==>
        TypeCheckE(g, expr).typ.BoolT? &&
        TypeCheckE(g, expr.leftG).Type? &&
        TypeCheckE(g, expr.leftG).typ.NumT? &&
        TypeCheckE(GammaWithoutMovedE(g, expr.leftG), expr.rightG).Type? &&
        TypeCheckE(GammaWithoutMovedE(g, expr.leftG), expr.rightG).typ.NumT?;
ensures TypeCheckE(g, expr).Type? && expr.Eq? ==>
        TypeCheckE(g, expr).typ.BoolT? &&
        TypeCheckE(g, expr.leftE).Type? &&
        (TypeCheckE(g, expr.leftE).typ.NumT? || TypeCheckE(g, expr.leftE).typ.BoolT?) &&
        TypeCheckE(GammaWithoutMovedE(g, expr.leftE), expr.rightE).Type? &&
        TypeCheckE(g, expr.leftE).typ ==
        TypeCheckE(GammaWithoutMovedE(g, expr.leftE), expr.rightE).typ;
{
  match expr {

    case V(val) => (
      Type(g, TypeCheckV(val))
    )

    case Var(x) =>
      if x in g then (
        if MoveType(g[x]) then (
          var g2 :=  (map y | y in g && x != y :: g[y]);
          assert g2 == GammaWithoutMovedE(g, expr);
          Type(g2, g[x])
        ) else (
          Type(g, g[x])
        )
      ) else (
        Fail
      )

    case Add(l, r) =>
      match TypeCheckE(g, l) {
        case Type(g1, lt) => if !lt.NumT? then Fail else match TypeCheckE(g1, r) {
          case Type(g2, rt) => if !rt.NumT? then Fail else (
            Type(g2, NumT)
          )
          case Fail => Fail
        }
        case Fail => Fail
      }

    case GT(l, r) =>
      match TypeCheckE(g, l) {
        case Type(g1, lt) => if !lt.NumT? then Fail else match TypeCheckE(g1, r) {
          case Type(g2, rt) => if !rt.NumT? then Fail else (
            Type(g2, BoolT)
          )
          case Fail => Fail
        }
        case Fail => Fail
      }

    case Eq(l, r) =>
      match TypeCheckE(g, l) {
        case Type(g1, lt) => match TypeCheckE(g1, r) {
          case Type(g2, rt) => if !lt.RefT? && lt == rt then (
            Type(g2, BoolT)
          ) else (
            Fail
          )
          case Fail => Fail
        }
        case Fail => Fail
      }

  }
}

function method TypeCheckS(g: Gamma, stmt: Stmt): Option<Gamma>
decreases stmt;
ensures TypeCheckS(g, stmt).Some? ==> GammaDeclarationsS(g, stmt);
ensures TypeCheckS(g, stmt).Some? ==> g !! DeclaredVars(stmt);
ensures TypeCheckS(g, stmt).Some? ==> g !! ScopedVars(stmt);
ensures TypeCheckS(g, stmt).Some? ==>
        TypeCheckS(g, stmt).val ==
        GammaUnion(GammaWithoutMovedS(g, stmt), ScopedVars(stmt));
ensures TypeCheckS(g, stmt).Some? && stmt.VarDecl? ==>
        stmt.x !in g &&
        TypeCheckE(g, stmt.vinit).Type? && TypeCheckE(g, stmt.vinit).typ == stmt.vtype;
ensures TypeCheckS(g, stmt).Some? && stmt.Assign? ==>
        TypeCheckE(g, stmt.expr).Type? &&
        stmt.y in TypeCheckE(g, stmt.expr).gamma &&
        TypeCheckE(g, stmt.expr).typ == TypeCheckE(g, stmt.expr).gamma[stmt.y];
ensures TypeCheckS(g, stmt).Some? && stmt.If? ==>
        TypeCheckE(g, stmt.cond).Type? &&
        TypeCheckE(g, stmt.cond).typ == BoolT &&
        TypeCheckS(TypeCheckE(g, stmt.cond).gamma, stmt.the).Some? &&
        TypeCheckS(TypeCheckE(g, stmt.cond).gamma, stmt.els).Some? &&
        DeclaredVars(stmt.the) !! DeclaredVars(stmt.els) &&
        g !! DeclaredVars(stmt.els);
ensures TypeCheckS(g, stmt).Some? && stmt.While? ==>
        TypeCheckE(g, stmt.wcond).Type? &&
        TypeCheckE(g, stmt.wcond).typ.BoolT? &&
        TypeCheckS(TypeCheckE(g, stmt.wcond).gamma, stmt.wbody).Some? &&
        GammaWithoutMovedS(GammaWithoutMovedE(g, stmt.wcond), stmt.wbody) == g &&
        DeclaredVars(stmt.wbody) == map[];
ensures TypeCheckS(g, stmt).Some? && stmt.Seq? ==>
        TypeCheckS(g, stmt.s1).Some? &&
        TypeCheckS(TypeCheckS(g, stmt.s1).val, stmt.s2).Some? &&
        DeclaredVars(stmt.s1) !! DeclaredVars(stmt.s2);
ensures TypeCheckS(g, stmt).Some? && stmt.Skip? ==> g == TypeCheckS(g, stmt).val;
{
  match stmt {

    case VarDecl(x, vtype, vinit) =>
      if x in g then
        None
      else
        match TypeCheckE(g, vinit) {
          case Type(g2, vt) =>
            if vt == vtype then (
              assert g !! DeclaredVars(stmt);
              assert GammaDeclarationsS(g, stmt);
              assert g2[x := vt] == GammaUnion(GammaWithoutMovedS(g, stmt), ScopedVars(stmt));
              Some(g2[x := vt])
            ) else None
          case Fail => None
        }

    case Assign(y, expr) =>
      match TypeCheckE(g, expr) {
        case Type(g2, ct) => (
          if y !in g2 || g[y] != ct then None else
            Some(g2[y := ct])
        )
        case Fail => None
      }

    case If(con, the, els) =>
      match TypeCheckE(g, con) {
        case Type(g2, ct) => if !ct.BoolT? then None else match TypeCheckS(g2, the) {
          case Some(g3) => match TypeCheckS(g2, els) {
            case Some(g4) => if !(g !! DeclaredVars(the)) || !(g !! DeclaredVars(els)) || !(DeclaredVars(the) !! DeclaredVars(els)) then None else (
              assert g !! DeclaredVars(stmt);
              assert GammaDeclarationsE(g, con);
              assert GammaDeclarationsS(g2, the);
              assert GammaDeclarationsS(g2, els);
              assert GammaDeclarationsS(g, stmt);

              assert g2 == GammaWithoutMovedE(g, con);
              assert g3 == GammaUnion(GammaWithoutMovedS(g2, the), ScopedVars(the));
              assert g4 == GammaUnion(GammaWithoutMovedS(g2, els), ScopedVars(els));

              assert GammaJoin(g2, g3) == GammaWithoutMovedS(GammaWithoutMovedE(g, con), the);

              assert GammaJoin(GammaJoin(g2, g3), g4) ==
                     GammaWithoutMovedS(GammaWithoutMovedS(GammaWithoutMovedE(g, con), the), els);

              GammaWithoutMovedIfDistribution(g, con, the, els);

              assert GammaJoin(GammaJoin(g2, g3), g4) ==
                     GammaWithoutMovedS(g, stmt);
              assert GammaJoin(GammaJoin(g2, g3), g4) == GammaUnion(GammaWithoutMovedS(g, stmt), ScopedVars(stmt));
              Some(GammaJoin(GammaJoin(g2, g3), g4))
            )
            case None => None
          }
          case None => None
        }
        case Fail => None
      }

    case CleanUp(gs, refs, decls) => (
      assert g !! DeclaredVars(stmt);
      assert GammaWithoutMovedS(g, stmt) == GammaUnion(GammaWithoutMovedS(g, stmt), ScopedVars(stmt));
      Some(GammaWithoutMovedS(g, stmt)))

    case While(con, body) =>
      match TypeCheckE(g, con) {
        case Type(g2, ct) => if !ct.BoolT? then None else match TypeCheckS(g2, body) {
          case Some(g3) => if GammaJoin(g2, g3) != g || DeclaredVars(body) != map[] then None else (
            assert g3 == GammaUnion(GammaWithoutMovedS(GammaWithoutMovedE(g, con), body), ScopedVars(body));
            assert GammaJoin(g2, g3) == GammaWithoutMovedS(GammaWithoutMovedE(g, con), body);
            assert ScopedVars(stmt) == map[];
            assert GammaUnion(GammaWithoutMovedS(g, stmt), ScopedVars(stmt)) == GammaWithoutMovedS(g, stmt);
            GammaWithoutMovedWhileDistribution(g, con, body);
            assert GammaJoin(g2, g3) == GammaWithoutMovedS(g, stmt);
            Some(GammaJoin(g2, g3)))
          case None => None
        }
        case Fail => None
      }

    case Seq(s1, s2) =>
      match TypeCheckS(g, s1) {
        case Some(g2) => match TypeCheckS(g2, s2) {
          case Some(g3) => if !(DeclaredVars(s1) !! DeclaredVars(s2)) then (
            None
          ) else if !(g !! DeclaredVars(s2)) then (
            None
          ) else (
            assert g !! DeclaredVars(stmt);
            assert GammaDeclarationsS(g, stmt);
            assert g2 == GammaUnion(GammaWithoutMovedS(g, s1), ScopedVars(s1));
            assert g3 == GammaUnion(GammaWithoutMovedS(g2, s2), ScopedVars(s2));

            assert g3 == GammaUnion(
              GammaWithoutMovedS(GammaUnion(GammaWithoutMovedS(g, s1), ScopedVars(s1)), s2),
              ScopedVars(s2));
            assert g3 == GammaUnion(
              GammaWithoutMovedS(GammaUnion(GammaWithoutMovedS(g, s1), ScopedVars(s1)), s2),
              ScopedVars(s2));
            assert g3 == GammaUnion(
              GammaWithoutMovedS(GammaWithoutMovedS(g, s1), s2),
              ScopedVars(stmt));

            GammaWithoutMovedSeqDistribution(g, s1, s2);

            assert g3 == GammaUnion(GammaWithoutMovedS(g, stmt), ScopedVars(stmt));
            Some(g3)
          )
          case None => None
        }
        case None => None
      }

    case Skip => (
      assert g == GammaUnion(GammaWithoutMovedS(g, stmt), ScopedVars(stmt));
      Some(g)
    )
  }
}

// --------- Evaluating ---------

type Sigma = map<string, Value>

function method SigmaWithoutMovedS(s: Sigma, stmt: Stmt): Sigma
decreases stmt;
ensures forall x :: x in SigmaWithoutMovedS(s, stmt) ==> x in s;
{
  map x | x in s && !(x in ReferencedVarsSDec(stmt, 0) && MoveType(TypeCheckV(s[x])))
                 && !(x in ConsumedVarsS(stmt, 0)) :: s[x]
}

function method TypeSigma(s: Sigma): Gamma
ensures forall x :: x in s <==> x in TypeSigma(s);
ensures forall x :: x in s ==> TypeCheckV(s[x]) == TypeSigma(s)[x];
{
  map x | x in s :: TypeCheckV(s[x])
}

function method EvalE(sig: Sigma, expr: Expr): (Sigma, Expr)
requires !expr.V?;
requires TypeCheckE(TypeSigma(sig), expr).Type?;
ensures forall x :: x in EvalE(sig, expr).0 ==> x in sig && EvalE(sig, expr).0[x] == sig[x];
ensures TypeCheckE(TypeSigma(sig), expr) ==
        TypeCheckE(TypeSigma(EvalE(sig, expr).0), EvalE(sig, expr).1);
{

  ghost var g := TypeCheckE(TypeSigma(sig), expr);

  match expr {

    case Var(x) => (
      assert x in sig;
      if MoveType(TypeSigma(sig)[x]) then (
        var sig2 := map y | y in sig && x != y :: sig[y];
        assert TypeCheckE(TypeSigma(sig2), V(sig[x])).Type?;
        assert TypeCheckE(TypeSigma(sig2), V(sig[x])).gamma == TypeSigma(sig2);
        assert x in ReferencedVarsE(expr);
        assert x !in g.gamma;
        assert x !in sig2;
        assert x !in TypeSigma(sig2);
        assert g.gamma == TypeSigma(sig2);
        assert g == TypeCheckE(TypeSigma(sig2), V(sig[x]));
        (sig2, V(sig[x]))
      ) else (
        assert TypeCheckE(TypeSigma(sig), V(sig[x])).Type?;
        assert g == TypeCheckE(TypeSigma(sig), V(sig[x]));
        (sig, V(sig[x]))
      )
    )

    case Add(l, r) =>
      if !l.V? then (
        assert TypeCheckE(TypeSigma(sig), l).Type?;
        var (sig2, l2) := EvalE(sig, l);
        assert g == TypeCheckE(TypeSigma(sig2), Add(l2, r));
        (sig2, Add(l2, r))
      ) else if !r.V? then (
        var (sig2, r2) := EvalE(sig, r);
        assert g == TypeCheckE(TypeSigma(sig2), Add(l, r2));
        (sig2, Add(l, r2))
      ) else (
        assert g == TypeCheckE(TypeSigma(sig), V(Num(l.val.nval + r.val.nval)));
        (sig, V(Num(l.val.nval + r.val.nval)))
      )

    case GT(l, r) =>
      if !l.V? then (
        assert TypeCheckE(TypeSigma(sig), l).Type?;
        var (sig2, l2) := EvalE(sig, l);
        assert g == TypeCheckE(TypeSigma(sig2), GT(l2, r));
        (sig2, GT(l2, r))
      ) else if !r.V? then (
        var (sig2, r2) := EvalE(sig, r);
        assert g == TypeCheckE(TypeSigma(sig2), GT(l, r2));
        (sig2, GT(l, r2))
      ) else (
        assert g == TypeCheckE(TypeSigma(sig), V(Bool(l.val.nval > r.val.nval)));
        (sig, V(Bool(l.val.nval > r.val.nval)))
      )

    case Eq(l, r) =>
      if !l.V? then (
        var (sig2, l2) := EvalE(sig, l);
        assert g == TypeCheckE(TypeSigma(sig2), Eq(l2, r));
        (sig2, Eq(l2, r))
      ) else if !r.V? then (
        var (sig2, r2) := EvalE(sig, r);
        assert g == TypeCheckE(TypeSigma(sig2), Eq(l, r2));
        (sig2, Eq(l, r2))
      ) else if l.val.Num? && r.val.Num? then (
        assert g == TypeCheckE(TypeSigma(sig), V(Bool(l.val.nval == r.val.nval)));
        (sig, V(Bool(l.val.nval == r.val.nval)))
      ) else (
        assert g == TypeCheckE(TypeSigma(sig), V(Bool(l.val.bval == r.val.bval)));
        (sig, V(Bool(l.val.bval == r.val.bval)))
      )

  }
}

predicate IfConversion1(g: Gamma, x: string, the: Stmt, els: Stmt)
requires x !in ScopedVars(the);
requires x in GammaWithoutMovedS(g, If(V(Bool(true)), the, els));
ensures x in GammaWithoutMovedS(
          GammaUnion(GammaWithoutMovedS(g, the), ScopedVars(the)),
          CleanUp(g, els, the))
{
  var stmt := If(V(Bool(true)), the, els);
  assert x in g;
  assert !(x in ConsumedVarsS(stmt, 0));
  assert x !in ConsumedVarsS(the, 1) + ConsumedVarsS(els, 1);
  assert x !in ConsumedVarsS(the, 1);
  assert x !in ConsumedVarsS(the, 0);
  assert x !in ConsumedVarsS(els, 1);
  assert x !in ConsumedVarsS(els, 0);


  if MoveType(g[x]) then (
    assert x !in ReferencedVarsS(stmt);
    assert x !in ReferencedVarsSDec(stmt, 0);
    assert x !in ReferencedVarsE(V(Bool(true))) + ReferencedVarsS(the) + ReferencedVarsS(els);
    assert x !in ReferencedVarsS(the) + ReferencedVarsS(els);
    assert x !in ReferencedVarsS(the);
    assert x !in ReferencedVarsS(els);
    assert x !in ReferencedVarsS(CleanUp(g, els, the));
    assert x !in (ReferencedVarsS(els) - ReferencedVarsS(the));
    assert x !in ConsumedVarsS(CleanUp(g, els, the), 0);

    assert x in GammaWithoutMovedS(g, the);
    assert x in GammaUnion(GammaWithoutMovedS(g, the), ScopedVars(the));
    true
  ) else (
    assert x !in ConsumedVarsS(CleanUp(g, els, the), 0);
    assert x in GammaWithoutMovedS(g, the);
    assert x in GammaUnion(GammaWithoutMovedS(g, the), ScopedVars(the));
    true
  )
}

predicate IfConversion2(g: Gamma, x: string, the: Stmt, els: Stmt)
requires x in GammaWithoutMovedS(
          GammaUnion(GammaWithoutMovedS(g, the), ScopedVars(the)),
          CleanUp(g, els, the))
ensures x in GammaWithoutMovedS(g, If(V(Bool(true)), the, els));
{
  var stmt := If(V(Bool(true)), the, els);
  assert x !in ConsumedVarsS(CleanUp(g, els, the), 0);

  assert ConsumedVarsS(CleanUp(g, els, the), 0) ==
      (set x | x in ScopedVars(the)) + (set x | x in ReferencedVarsS(els) && x in g && MoveType(g[x]))
                                     + ConsumedVarsS(els, 1);
  assert x !in (set x | x in ScopedVars(the))
             + (set x | x in ReferencedVarsS(els) && x in g && MoveType(g[x]))
             + ConsumedVarsS(els, 1);
  assert x !in (set x | x in ScopedVars(the));
  assert x !in ScopedVars(the);

  assert x in GammaWithoutMovedS(g, the);

  assert x !in ConsumedVarsS(els, 0);

  assert x in GammaUnion(GammaWithoutMovedS(g, the), ScopedVars(the));
  assert x in GammaWithoutMovedS(g, the);
  assert x !in ConsumedVarsS(the, 0);
  assert x !in ConsumedVarsS(the, 0) + ConsumedVarsS(els, 0);
  assert x !in ConsumedVarsS(stmt, 0);
  assert x in g;

  if MoveType(g[x]) then (
    assert x !in ReferencedVarsSDec(the, 0);
    assert x !in ReferencedVarsSDec(CleanUp(g, els, the), 0);
    assert x !in ReferencedVarsS(the);
    assert x !in ReferencedVarsS(els);
    assert x !in ReferencedVarsS(the) + ReferencedVarsS(els);
    assert x !in ReferencedVarsS(stmt);
    assert x in GammaWithoutMovedS(g, stmt);
    true
  ) else (
    assert x !in ConsumedVarsS(els, 0);
    assert !(x in ConsumedVarsS(stmt, 0));
    assert x in GammaWithoutMovedS(g, stmt);
    true
  )
}

predicate IfConversionE1(g: Gamma, x: string, the: Stmt, els: Stmt)
requires x !in ScopedVars(els);
requires x in GammaWithoutMovedS(g, If(V(Bool(false)), the, els));
ensures x in GammaWithoutMovedS(
          GammaUnion(GammaWithoutMovedS(g, els), ScopedVars(els)),
          CleanUp(g, the, els))
{
  var stmt := If(V(Bool(false)), the, els);
  assert x in g;
  assert !(x in ConsumedVarsS(stmt, 0));
  assert x !in ConsumedVarsS(the, 1) + ConsumedVarsS(els, 1);
  assert x !in ConsumedVarsS(the, 1);
  assert x !in ConsumedVarsS(the, 0);
  assert x !in ConsumedVarsS(els, 1);
  assert x !in ConsumedVarsS(els, 0);


  if MoveType(g[x]) then (
    assert x !in ReferencedVarsS(stmt);
    assert ReferencedVarsS(stmt) == ReferencedVarsE(V(Bool(false))) + ReferencedVarsS(the) + ReferencedVarsS(els);
    assert x !in ReferencedVarsE(V(Bool(false))) + ReferencedVarsS(the) + ReferencedVarsS(els);
    assert x !in ReferencedVarsS(the);
    assert x !in ReferencedVarsS(els);
    assert x !in ReferencedVarsS(CleanUp(g, the, els));
    assert x !in ReferencedVarsS(els);
    assert x !in ConsumedVarsS(CleanUp(g, the, els), 0);

    assert x in GammaWithoutMovedS(g, els);
    assert x in GammaUnion(GammaWithoutMovedS(g, els), ScopedVars(els));
    true
  ) else (
    assert x !in ConsumedVarsS(CleanUp(g, the, els), 0);
    assert x in GammaWithoutMovedS(g, els);
    assert x in GammaUnion(GammaWithoutMovedS(g, els), ScopedVars(els));
    true
  )
}

predicate IfConversionE2(g: Gamma, x: string, the: Stmt, els: Stmt)
requires x in GammaWithoutMovedS(
          GammaUnion(GammaWithoutMovedS(g, els), ScopedVars(els)),
          CleanUp(g, the, els))
ensures x in GammaWithoutMovedS(g, If(V(Bool(false)), the, els));
{
  var stmt := If(V(Bool(false)), the, els);
  assert x !in ConsumedVarsS(CleanUp(g, the, els), 0);

  assert  ConsumedVarsS(CleanUp(g, the, els), 0) ==
      (set x | x in ScopedVars(els)) + (set x | x in ReferencedVarsS(the) && x in g && MoveType(g[x]))
                                     + ConsumedVarsS(the, 1);
  assert x !in (set x | x in ScopedVars(els))
             + (set x | x in ReferencedVarsS(the) && x in g && MoveType(g[x]))
             + ConsumedVarsS(the, 1);
  assert x !in (set x | x in ScopedVars(els));
  assert x !in ScopedVars(els);
  assert x !in ConsumedVarsS(the, 0);

  assert x in GammaUnion(GammaWithoutMovedS(g, els), ScopedVars(els));
  assert x in GammaWithoutMovedS(g, els);
  assert x !in ConsumedVarsS(els, 0);
  assert x !in ConsumedVarsS(stmt, 0);
  assert x in g;

  if MoveType(g[x]) then (
    assert x !in ReferencedVarsSDec(CleanUp(g, the, els), 0);
    assert x !in ReferencedVarsS(CleanUp(g, the, els));
    assert x !in ReferencedVarsE(V(Bool(false)));
    assert x !in ReferencedVarsS(the);
    assert x !in ReferencedVarsS(els);
    assert x !in ReferencedVarsE(V(Bool(false))) + ReferencedVarsS(the) + ReferencedVarsS(els);
    assert x !in ReferencedVarsS(stmt);
    assert x in GammaWithoutMovedS(g, stmt);
    true
  ) else (
    assert x !in ConsumedVarsS(the, 0);
    assert !(x in ConsumedVarsS(stmt, 0));
    assert x in GammaWithoutMovedS(g, stmt);
    true
  )
}

function method EvalS(sig: Sigma, stmt: Stmt): (Sigma, Stmt)
decreases stmt;
requires !stmt.Skip?;
requires TypeCheckS(TypeSigma(sig), stmt).Some?;
ensures forall x :: x in EvalS(sig, stmt).0 ==> x in sig || x in DeclaredVars(stmt);
ensures forall x :: x in DeclaredVars(EvalS(sig, stmt).1) ==> x in DeclaredVars(stmt);
ensures TypeCheckS(TypeSigma(sig), stmt) ==
        TypeCheckS(TypeSigma(EvalS(sig, stmt).0), EvalS(sig, stmt).1);
{
  ghost var g := TypeCheckS(TypeSigma(sig), stmt).val;

  match stmt {

    case VarDecl(x, vt, vinit) =>
      if !vinit.V? then (
        var (sig2, vinit2) := EvalE(sig, vinit);
        ghost var vet := TypeCheckE(TypeSigma(sig2), vinit2);
        assert vet.Type?;
        assert vet.typ == TypeCheckE(TypeSigma(sig), vinit).typ;
        assert vet.gamma == TypeCheckE(TypeSigma(sig), vinit).gamma;

        assert vt == vet.typ;
        assert stmt.x !in TypeSigma(sig);
        assert stmt.x !in TypeSigma(sig2);

        ghost var g2 := TypeCheckS(TypeSigma(sig2), VarDecl(x, vt, vinit2));
        assert g2.Some?;
        assert g == g2.val;
        assert forall x :: x in sig2 ==> x in sig || x in DeclaredVars(stmt);
        (sig2, VarDecl(x, vt, vinit2))
      ) else (
        ghost var g2 := TypeCheckS(TypeSigma(sig[x := vinit.val]), Skip);
        assert g2.Some?;
        assert g == g2.val;
        assert forall z :: z in sig[x := vinit.val] ==> z in sig || z in DeclaredVars(stmt);
        (sig[x := vinit.val], Skip)
      )

    case Assign(y, expr) =>
      if !expr.V? then (
        var (sig2, expr2) := EvalE(sig, expr);
        ghost var vet := TypeCheckE(TypeSigma(sig2), expr2);
        assert vet.Type?;
        assert vet.typ == TypeCheckE(TypeSigma(sig), expr).typ;
        assert vet.gamma == TypeCheckE(TypeSigma(sig), expr).gamma;
        assert stmt.y in TypeSigma(sig);
        /* assert stmt.y in TypeSigma(sig2); */
        assert TypeSigma(sig)[y] == vet.typ;
        assert TypeSigma(sig2)[y] == vet.typ;
        ghost var g2 := TypeCheckS(TypeSigma(sig2), Assign(y, expr2));
        assert g2.Some?;
        assert g == g2.val;
        assert forall x :: x in sig2 ==> x in sig || x in DeclaredVars(stmt);
        (sig2, Assign(y, expr2))
      ) else (
        ghost var g2 := TypeCheckS(TypeSigma(sig[y := expr.val]), Skip);
        assert g2.Some?;
        assert g == g2.val;
        assert forall z :: z in sig[y := expr.val] ==> z in sig || z in DeclaredVars(stmt);
        (sig[y := expr.val], Skip)
      )

    case If(cond, the, els) =>
      if !cond.V? then (
        var (sig2, cond2) := EvalE(sig, cond);
        ghost var g2 := TypeCheckS(TypeSigma(sig2), If(cond2, the, els));
        assert g2.Some?;
        assert g == g2.val;
        assert forall x :: x in sig2 ==> x in sig || x in DeclaredVars(stmt);
        (sig2, If(cond2, the, els))
      ) else if cond.val.bval then (
        ghost var gs := TypeSigma(sig);
        assert g == GammaWithoutMovedS(gs, If(V(Bool(true)), the, els));
        ghost var g2 := TypeCheckS(gs, Seq(the, CleanUp(gs, els, the)));

        assert TypeCheckE(gs, cond).Type?;
        assert TypeCheckE(gs, cond).gamma == gs;
        assert TypeCheckS(gs, the).Some?;
        ghost var g3 := TypeCheckS(gs, the).val;
        assert TypeCheckS(g3, CleanUp(gs, els, the)).Some?;
        assert g2 == TypeCheckS(g3, CleanUp(gs, els, the));
        assert g2.Some?;
        assert g2.val == GammaWithoutMovedS(
          GammaUnion(GammaWithoutMovedS(gs, the), ScopedVars(the)),
          CleanUp(gs, els, the));

        assert g !! ScopedVars(the);
        assert forall x :: x in g ==> IfConversion1(gs, x, the, els) && x in g2.val;
        assert forall x :: x in g2.val ==> IfConversion2(gs, x, the, els) && x in g;

        assert g == g2.val;
        (sig, Seq(the, CleanUp(TypeSigma(sig), els, the)))

      ) else (
        ghost var gs := TypeSigma(sig);
        assert g == GammaWithoutMovedS(gs, If(V(Bool(false)), the, els));
        ghost var g2 := TypeCheckS(gs, Seq(els, CleanUp(gs, the, els)));

        assert TypeCheckE(gs, cond).Type?;
        assert TypeCheckE(gs, cond).gamma == gs;
        assert TypeCheckS(gs, els).Some?;
        ghost var g3 := TypeCheckS(gs, els).val;
        assert TypeCheckS(g3, CleanUp(gs, the, els)).Some?;
        assert g2 == TypeCheckS(g3, CleanUp(gs, the, els));
        assert g2.Some?;
        assert g2.val == GammaWithoutMovedS(
          GammaUnion(GammaWithoutMovedS(gs, els), ScopedVars(els)),
          CleanUp(gs, the, els));

        assert g !! ScopedVars(els);
        assert forall x :: x in g ==> IfConversionE1(gs, x, the, els) && x in g2.val;
        assert forall x :: x in g2.val ==> IfConversionE2(gs, x, the, els) && x in g;

        assert g == g2.val;
        (sig, Seq(els, CleanUp(TypeSigma(sig), the, els)))
      )

    case While(cond, body) => (
      ghost var gs := TypeSigma(sig);
      assert TypeCheckE(gs, cond).Type?;
      assert TypeCheckE(gs, cond).typ == BoolT;
      ghost var g2 := TypeCheckE(gs, cond).gamma;
      assert g2 == GammaWithoutMovedE(gs, cond);
      // can type check cond

      assert TypeCheckE(g2, V(Bool(true))).Type?;
      assert TypeCheckE(g2, V(Bool(true))).typ == BoolT;
      assert TypeCheckE(g2, V(Bool(true))).gamma == g2;
      // can type check V(Bool(true))

      assert TypeCheckS(g2, body).Some?;
      // can type check body

      assert TypeCheckS(g2, Skip).Some?;
      assert TypeCheckS(g2, Skip).val == g2;
      assert TypeCheckS(g2, If(V(Bool(true)), body, Skip)).Some?;
      ghost var g3 := TypeCheckS(g2, If(V(Bool(true)), body, Skip)).val;
      assert g3 == GammaWithoutMovedS(g2, body);
      // can type check    If(V(Bool(true)), body, Skip)

      assert TypeCheckS(gs, While(cond, body)).Some?;
      assert g == GammaWithoutMovedS(g, stmt);

      assert g3 ==
        GammaJoin(GammaWithoutMovedE(g, stmt.wcond),
                  GammaWithoutMovedS(GammaWithoutMovedE(g, stmt.wcond), stmt.wbody));



      assert TypeCheckS(g2, stmt.wbody).val ==
        GammaUnion(GammaWithoutMovedS(g, stmt), ScopedVars(body));
      assert gs == g3;

      assert TypeCheckS(g3, While(cond, body)).Some?;
      assert TypeCheckS(g3, While(cond, body)).val == g3;

      // can type check   While(cond, body)

      assert DeclaredVars(If(V(Bool(true)), body, Skip)) !! DeclaredVars(While(cond, body));
      assert g !! DeclaredVars(While(cond, body));
      assert TypeCheckS(g2, Seq(If(V(Bool(true)), body, Skip),
                                While(cond, body))).Some?;

      // can typo check the
      // can type check else
      // can type check if

      ghost var g4 := TypeCheckS(gs, If(cond,
               Seq(If(V(Bool(true)), body, Skip),
                   While(cond, body)), Skip));

      assert g4.Some?;
      assert g == g4.val;
      assert DeclaredVars(stmt) == DeclaredVars(body);
      assert DeclaredVars(body) == DeclaredVars(If(V(Bool(true)), body, Skip));
      assert DeclaredVars(stmt) == DeclaredVars(If(cond,
               Seq(If(V(Bool(true)), body, Skip),
                   While(cond, body)),
               Skip));
      (sig, If(cond,
               Seq(If(V(Bool(true)), body, Skip),
                   While(cond, body)),
               Skip))
    )

    case CleanUp(gs, refs, decls) => (
      ghost var g2 := TypeCheckS(TypeSigma(SigmaWithoutMovedS(sig, stmt)), Skip);
      assert g2.Some?;
      assert g == g2.val;
      assert forall x :: x in SigmaWithoutMovedS(sig, stmt) ==> x in sig || x in DeclaredVars(stmt);
      (SigmaWithoutMovedS(sig, stmt), Skip)
    )

    case Seq(s1, s2) =>
      if s1.Skip? then (
        ghost var g2 := TypeCheckS(TypeSigma(sig), s2);
        assert g2.Some?;
        (sig, s2)
      ) else (
        var (sig2, s12) := EvalS(sig, s1);
        assert TypeCheckS(TypeSigma(sig), s1).Some?;
        ghost var g2 := TypeCheckS(TypeSigma(sig), s1).val;
        assert TypeCheckS(g2, s2).Some?;

        assert TypeCheckS(TypeSigma(sig2), s12).Some?;
        ghost var g3 := TypeCheckS(TypeSigma(sig2), s12).val;
        assert GammaExtends(g2, g3);
        assert TypeSigma(sig) !! DeclaredVars(s2);
        assert TypeSigma(sig2) !! DeclaredVars(s2);
        assert DeclaredVars(s12) !! DeclaredVars(s2);

        ghost var g4 := TypeCheckS(TypeSigma(sig2), Seq(s12, s2));
        assert g4.Some?;
        assert g == g4.val;
        assert forall x :: x in sig2 ==> x in sig || x in DeclaredVars(stmt);
        (sig2, Seq(s12, s2))
      )

  }
}

// --------- Testing ---------

method TestVars() {
  assert TypeCheckE(map[], Var("x")).Fail?;
  ghost var t1 := TypeCheckE(map["x" := BoolT], Var("x"));
  assert t1.Type?;
  assert t1.typ == BoolT;
  assert t1.gamma == map["x" := BoolT];
}

method TestAdd() {
  assert TypeCheckE(map[], Add(V(Num(12)), V(Bool(false)))).Fail?;
  ghost var t1 := TypeCheckE(map[], Add(V(Num(12)), V(Num(23))));
  assert t1.Type?;
  assert t1.typ == NumT;
}

method TestVarDecl() {
  assert TypeCheckS(map[], VarDecl("x", NumT, V(Bool(false)))).None?;
  ghost var t1 := TypeCheckS(map[], VarDecl("x", NumT, V(Num(12))));
  assert t1.Some?;
  assert t1.val == map["x" := NumT];
}

/* method TestIf() { */
/*   ghost var prog := If(Eq(V(Num(12)), V(Num(4))), */
/*                        VarDecl("x", NumT, V(Num(1))), */
/*                        VarDecl("y", NumT, V(Num(2)))); */
/*   ghost var t1 := TypeCheckS(map[], prog); */
/*   assert t1.Some?; */
/*   assert t1.val == map[]; */
/* } */

/* method TestSeq() { */
/*   ghost var prog := Seq(VarDecl("x", NumT, V(Num(1))), */
/*                         VarDecl("x", NumT, V(Num(2)))); */
/*   assert TypeCheckS(map[], prog).None?; */

/*   ghost var prog2 := Seq(VarDecl("x", NumT, V(Num(1))), */
/*                          VarDecl("y", BoolT, V(Bool(false)))); */

/*   assert "y" !in map["x" := NumT]; */
/*   ghost var t1 := TypeCheckS(map[], prog2); */
/*   assert t1.Some?; */
/*   assert t1.val == map["x" := NumT, "y" := BoolT]; */
/* } */

// --------- Running ---------

method Main() {
  var prog: Option<Stmt> := Parse();
  if prog.None? {
    print "Parse error!\n";
    return;
  }
  var t: Option<Gamma> := TypeCheckS(TypeSigma(map[]), prog.val);
  if t.None? {
    print "Type error!\n";
    return;
  }
  print "Type checking succesful.\nEvaluating...\n";
  var n:nat := 0;
  var env: Sigma := map[];
  var s: Stmt := prog.val;
  while n < 100000 && !s.Skip?
  invariant TypeCheckS(TypeSigma(env), s).Some?;
  {
    var res := EvalS(env, s);
    env := res.0;
    s := res.1;
    n := n + 1;
  }
  print "Ran ";
  print n;
  print " steps.\n\nFinal environment:\n";
  print env;
  print "\n";
}
