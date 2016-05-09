datatype Option<T> = None | Some(val: T)

datatype Type = NumT
              | BoolT
datatype LType = T(t: Type) | Invalid
datatype Value = Num(nval: int)
              | Bool(bval: bool)
datatype Expr = V(val: Value)
              | Var(name: string)
              | Add(leftA: Expr, rightA: Expr)
              | Eq(leftE: Expr, rightE: Expr)
datatype Stmt = VarDecl(x: string, vtype: Type, vinit: Expr)
              | If(cond: Expr, the: Stmt, els: Stmt)
              | While(wcond: Expr, wbody: Stmt)
              | Seq(s1: Stmt, s2: Stmt)
              | Skip

type Gamma = map<string, LType>

function method TypeJoin(t1: LType, t2: LType): LType
{
  if t1 != t2 then Invalid else t1
}

function method GammaJoin(g1: Gamma, g2: Gamma): Gamma {
  var g1k: set<string> := (set x | x in g1);
  var g2k: set<string> := (set x | x in g2);
  (map x | x in g1k + g2k ::
    if x in g1k && x in g2k then
      TypeJoin(g1[x], g2[x])
    else
      Invalid)
}

function method GammaUnion(g1: Gamma, g2: Gamma): Gamma {
  var g1k: set<string> := (set x | x in g1);
  var g2k: set<string> := (set x | x in g2);
  (map x | x in g1k + g2k ::
    if x in g1k && x in g2k then
      TypeJoin(g1[x], g2[x])
    else if x in g2k then
      g2[x]
    else
      g1[x])
}

predicate GammaExtends(gamma1: Gamma, gamma2: Gamma) {
  forall x :: x in gamma1 ==> x in gamma2 && (gamma2[x] == Invalid || gamma1[x] == gamma2[x])
}

predicate GammaExtendsInv(gamma1: Gamma, gamma2: Gamma) {
  (forall x :: x in gamma1 ==> x in gamma2) &&
  forall x :: x in gamma2 ==> x in gamma1 && (gamma2[x] == Invalid || gamma1[x] == gamma2[x])
}

predicate GammaExtendsAdd(gamma1: Gamma, gamma2: Gamma) {
  forall x :: x in gamma1 ==> x in gamma2 && gamma1[x] == gamma2[x]
}

predicate GammaDeclarationsE(g: Gamma, expr: Expr) {
  forall x ::x in ReferencedVarsE(expr) ==> x in g && !g[x].Invalid?
}

predicate GammaDeclarationsS(g: Gamma, stmt: Stmt)
requires NoDuplicateDeclarations(stmt);
{
  forall x ::x in ReferencedVarsS(stmt) ==> x in g && !g[x].Invalid?
}

predicate NoDuplicateDeclarations(stmt: Stmt)
decreases stmt;
{
  match stmt {
    case VarDecl(x, vtype, vinit) => true
    case If(con, the, els) => (
      NoDuplicateDeclarations(the) &&
      NoDuplicateDeclarations(els)
    )
    case While(con, body) => NoDuplicateDeclarations(body)
    case Seq(s1, s2) => (
      NoDuplicateDeclarations(s1) &&
      NoDuplicateDeclarations(s2) &&
      DeclaredVars(s1) !! DeclaredVars(s2)
    )
    case Skip => true
  }
}

function DeclaredVars(stmt: Stmt): Gamma
decreases stmt;
{
  match stmt {
    case VarDecl(x, vtype, vinit) => map[x := T(vtype)]
    case If(con, the, els) => GammaUnion(DeclaredVars(the), DeclaredVars(els))
    case While(con, body) => DeclaredVars(body)
    case Seq(s1, s2) => GammaUnion(DeclaredVars(s1), DeclaredVars(s2))
    case Skip => map[]
  }
}

predicate NoDuplicateReferencesE(expr: Expr) {
  match expr {
    case V(val) => true
    case Var(x) => true
    case Add(l, r) =>
      NoDuplicateReferencesE(l) &&
      NoDuplicateReferencesE(r) &&
      ReferencedVarsE(l) !! ReferencedVarsE(r)
    case Eq(l, r) =>
      NoDuplicateReferencesE(l) &&
      NoDuplicateReferencesE(r) &&
      ReferencedVarsE(l) !! ReferencedVarsE(r)
  }
}

predicate NoDuplicateReferencesS(stmt: Stmt)
{
  match stmt {
    case VarDecl(x, vtype, vinit) => NoDuplicateReferencesE(vinit)
    case If(con, the, els) => (
      NoDuplicateReferencesE(con) &&
      NoDuplicateReferencesS(the) &&
      NoDuplicateReferencesS(els) &&
      ReferencedVarsE(con) !! ReferencedVarsS(the) &&
      ReferencedVarsE(con) !! ReferencedVarsS(els)
    )
    case While(con, body) => (
      NoDuplicateReferencesE(con) &&
      NoDuplicateReferencesS(body) &&
      ReferencedVarsE(con) !! ReferencedVarsS(body)
    )
    case Seq(s1, s2) => (
      NoDuplicateReferencesS(s1) &&
      NoDuplicateReferencesS(s2) &&
      ReferencedVarsS(s1) !! ReferencedVarsS(s2)
    )
    case Skip => true
  }
}

function ReferencedVarsE(expr: Expr): Gamma
ensures forall x :: x in ReferencedVarsE(expr) ==> ReferencedVarsE(expr)[x].Invalid?;
{
  match expr {
    case V(val) => map[]
    case Var(x) => map[x := Invalid]
    case Add(l, r) => GammaUnion(ReferencedVarsE(l), ReferencedVarsE(r))
    case Eq(l, r) => GammaUnion(ReferencedVarsE(l), ReferencedVarsE(r))
  }
}

function ReferencedVarsS(stmt: Stmt): Gamma
ensures forall x :: x in ReferencedVarsS(stmt) ==> ReferencedVarsS(stmt)[x].Invalid?;
{
  match stmt {
    case VarDecl(x, vtype, vinit) =>
      ReferencedVarsE(vinit)
    case If(con, the, els) =>
      GammaUnion(GammaUnion(ReferencedVarsE(con), ReferencedVarsS(the)),
                 ReferencedVarsS(els))
    case While(con, body) =>
      GammaUnion(ReferencedVarsE(con), ReferencedVarsS(body))
    case Seq(s1, s2) => GammaUnion(
      ReferencedVarsS(s1),
      map x | x in ReferencedVarsS(s2) && x !in DeclaredVars(s1) :: ReferencedVarsS(s2)[x])
    case Skip => map[]
  }
}

predicate NoDuplicateScopeS(stmt: Stmt) {
  match stmt {
    case VarDecl(x, vtype, vinit) => NoDuplicateReferencesE(vinit)
    case If(con, the, els) => (
      NoDuplicateReferencesE(con) &&
      NoDuplicateScopeS(the) &&
      NoDuplicateScopeS(els) &&
      ReferencedVarsE(con) !! ScopedVarsS(the) &&
      ReferencedVarsE(con) !! ScopedVarsS(els)
    )
    case While(con, body) => (
      NoDuplicateReferencesE(con) &&
      NoDuplicateScopeS(body) &&
      ReferencedVarsE(con) !! ScopedVarsS(body)
    )
    case Seq(s1, s2) => (
      NoDuplicateScopeS(s1) &&
      NoDuplicateScopeS(s2) &&
      ScopedVarsS(s1) !! ScopedVarsS(s2)
    )
    case Skip => true
  }
}

function ScopedVarsS(stmt: Stmt): Gamma
ensures forall x :: x in ScopedVarsS(stmt) ==> ScopedVarsS(stmt)[x].Invalid?;
{
  match stmt {
    case VarDecl(x, vtype, vinit) =>
      ReferencedVarsE(vinit)
    case If(con, the, els) => (
      var g1k: set<string> := (set x | x in DeclaredVars(the));
      var g2k: set<string> := (set x | x in DeclaredVars(els));
      GammaUnion(GammaUnion(GammaUnion(ReferencedVarsE(con), ScopedVarsS(the)),
                            ScopedVarsS(els)),
                 (map x | x in g1k + g2k :: Invalid))
    )
    case While(con, body) =>
      GammaUnion(ReferencedVarsE(con), ScopedVarsS(body))
    case Seq(s1, s2) => GammaUnion(ScopedVarsS(s1), ScopedVarsS(s2))
    case Skip => map[]
  }
}

datatype TypeCheckERes = Fail | Type(gamma: Gamma, typ: Type)
function method TypeCheckV(val: Value): Type
{
  match val {
    case Num(_) => NumT
    case Bool(_) => BoolT
  }
}

function method TypeCheckE(g: Gamma, expr: Expr): TypeCheckERes
decreases expr;
ensures TypeCheckE(g, expr).Type? ==> NoDuplicateReferencesE(expr);
ensures TypeCheckE(g, expr).Type? ==> GammaDeclarationsE(g, expr);
ensures TypeCheckE(g, expr).Type? ==>
        forall x ::x in ReferencedVarsE(expr) ==> x in TypeCheckE(g, expr).gamma && TypeCheckE(g, expr).gamma[x].Invalid?;
ensures TypeCheckE(g, expr).Type? ==>
        GammaExtendsInv(g, GammaUnion(g, ReferencedVarsE(expr)));
ensures TypeCheckE(g, expr).Type? ==>
        GammaUnion(g, ReferencedVarsE(expr)) == TypeCheckE(g, expr).gamma;
ensures TypeCheckE(g, expr).Type? && expr.Add? ==>
        TypeCheckE(g, expr.leftA).Type? &&
        TypeCheckE(TypeCheckE(g, expr.leftA).gamma, expr.rightA).Type? &&
        ReferencedVarsE(expr.leftA) !! ReferencedVarsE(expr.rightA);
ensures TypeCheckE(g, expr).Type? && expr.Eq? ==>
        TypeCheckE(g, expr.leftE).Type? &&
        TypeCheckE(TypeCheckE(g, expr.leftE).gamma, expr.rightE).Type? &&
        ReferencedVarsE(expr.leftE) !! ReferencedVarsE(expr.rightE);
{
  match expr {

    case V(val) => (
      assert GammaUnion(g, ReferencedVarsE(expr)) == g;
      Type(g, TypeCheckV(val))
    )

    case Var(x) =>
      if x in g && !g[x].Invalid? then (
        assert GammaUnion(g, ReferencedVarsE(expr)) == (map y | y in g :: if x == y then Invalid else g[y]);
        Type((map y | y in g :: if x == y then Invalid else g[y]), g[x].t)
      ) else (
        Fail
      )

    case Add(l, r) =>
      match TypeCheckE(g, l) {
        case Type(g1, lt) => if !lt.NumT? then Fail else match TypeCheckE(g1, r) {
          case Type(g2, rt) => if !rt.NumT? then Fail else (
            assert GammaUnion(g, ReferencedVarsE(expr)) == g2;

            assert GammaUnion(g, ReferencedVarsE(l)) == g1;
            assert GammaExtendsInv(g, g1);

            assert GammaExtends(ReferencedVarsE(l), g1);

            assert ReferencedVarsE(l) !! ReferencedVarsE(r);
            Type(g2, NumT)
          )
          case Fail => Fail
        }
        case Fail => Fail
      }

    case Eq(l, r) =>
      match TypeCheckE(g, l) {
        case Type(g1, lt) => match TypeCheckE(g1, r) {
          case Type(g2, rt) => if lt == rt then (
            assert GammaUnion(g, ReferencedVarsE(expr)) == g2;
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

lemma GammaSeqUnion(g: Gamma, g2: Gamma, g3: Gamma, s1: Stmt, s2: Stmt)
requires DeclaredVars(s1) !! DeclaredVars(s2);
requires ScopedVarsS(s1) !! ScopedVarsS(s2);
requires g2 == GammaUnion(GammaUnion(g, DeclaredVars(s1)),
                          ScopedVarsS(s1));
requires g3 == GammaUnion(GammaUnion(g2, DeclaredVars(s2)),
                          ScopedVarsS(s2));
ensures g3 == GammaUnion(GammaUnion(g, DeclaredVars(Seq(s1, s2))), ScopedVarsS(Seq(s1, s2)));
{
  ghost var seqg1 := GammaUnion(GammaUnion(GammaUnion(GammaUnion(g,
                                                                 DeclaredVars(s1)),
                                                     ScopedVarsS(s1)),
                                           DeclaredVars(s2)),
                               ScopedVarsS(s2));
  assert g3 == seqg1;
  ghost var seqg2 := GammaUnion(GammaUnion(GammaUnion(GammaUnion(g,
                                                                 DeclaredVars(s1)),
                                                      DeclaredVars(s2)),
                                           ScopedVarsS(s1)),
                                ScopedVarsS(s2));
  assert seqg1 == seqg2;
  ghost var seqg3 := GammaUnion(GammaUnion(GammaUnion(g,
                                                      GammaUnion(DeclaredVars(s1),
                                                                 DeclaredVars(s2))),
                                           ScopedVarsS(s1)),
                                ScopedVarsS(s2));
  assert seqg2 == seqg3;
  ghost var seqg4 := GammaUnion(GammaUnion(g,
                                          GammaUnion(DeclaredVars(s1),
                                                     DeclaredVars(s2))),
                                GammaUnion(ScopedVarsS(s1),
                                           ScopedVarsS(s2)));
  assert seqg3 == seqg4;
  ghost var seqg5 := GammaUnion(GammaUnion(g, DeclaredVars(Seq(s1, s2))),
                                ScopedVarsS(Seq(s1, s2)));
  assert seqg4 == seqg5;
  assert g3 == seqg5;
}

/* lemma GammaUnionDist(g1: Gamma, g2: Gamma, g3: Gamma, g4: Gamma) */
/* requires g1 !! g2; */
/* requires g3 !! g4; */
/* requires forall x :: x in g1 ==> x in g3 && g1[x] == g3[x]; */
/* requires forall x :: x in g2 ==> x in g4 && g2[x] == g4[x]; */
/* ensures forall x :: x in GammaUnion(g1, g2) ==> x in GammaUnion(g3, g4) && */
/*                          GammaUnion(g1, g2)[x] == GammaUnion(g3, g4)[x]; */
/* { */
/* } */

/* lemma ScopedReferences(stmt: Stmt) */
/* requires stmt.If? ==> ReferencedVarsE(stmt.cond) !! ReferencedVarsS(stmt.the) && */
/*                       ReferencedVarsE(stmt.cond) !! ReferencedVarsS(stmt.els) && */
/*                       ReferencedVarsE(stmt.cond) !! ScopedVarsS(stmt.the) && */
/*                       ReferencedVarsE(stmt.cond) !! ScopedVarsS(stmt.els); */
/* ensures forall x :: x in ReferencedVarsS(stmt) ==> x in ScopedVarsS(stmt) && */
/*                     ReferencedVarsS(stmt)[x] == ScopedVarsS(stmt)[x]; */
/* { */
/*   match stmt { */
/*     case VarDecl(x, vtype, vinit) => {} */
/*     case If(con, the, els) => { */
/*       ScopedReferences(the); */
/*       assert forall x :: x in ReferencedVarsS(the) ==> x in ScopedVarsS(the) && ReferencedVarsS(the)[x] == ScopedVarsS(the)[x]; */

/*       ScopedReferences(els); */
/*       assert forall x :: x in ReferencedVarsS(els) ==> x in ScopedVarsS(els) && ReferencedVarsS(els)[x] == ScopedVarsS(els)[x]; */

/*       var g1 := GammaUnion(ReferencedVarsE(con), ReferencedVarsS(the)); */
/*       var g2 := GammaUnion(ReferencedVarsE(con), ScopedVarsS(the)); */
/*       GammaUnionDist(ReferencedVarsE(con), ReferencedVarsS(the), */
/*                      ReferencedVarsE(con), ScopedVarsS(the)); */
/*       assert forall x :: x in g1 ==> x in g2 && g1[x] == g2[x]; */

/*       assert forall x :: x in g1 ==> x in g2 && g1[x] == g2[x]; */

/*       assert forall x :: x in g1 ==> x in g2 && g1[x] == g2[x]; */

/*     } */
/*     case While(con, body) => { */
/*       ScopedReferences(body); */
/*     } */
/*     case Seq(s1, s2) => { */
/*       ScopedReferences(s1); */
/*       ScopedReferences(s2); */
/*     } */
/*     case Skip => {} */
/*   } */
/* } */

lemma ScopeUpperBound(s: Stmt)
ensures forall x :: x in ScopedVarsS(s) ==>
        (x in ReferencedVarsS(s) && ScopedVarsS(s)[x] == ReferencedVarsS(s)[x]) ||
        (x in DeclaredVars(s) && ScopedVarsS(s)[x].Invalid?);
{}

lemma GammaDisjoint(a: Gamma, b: Gamma, c: Gamma, d: Gamma)
requires forall x :: x in c ==> x in a || x in b;
requires a !! d;
requires b !! d;
ensures c !! d;
{}

lemma ScopeDisjointE(e: Expr, s: Stmt)
requires ReferencedVarsE(e) !! ReferencedVarsS(s);
requires ReferencedVarsE(e) !! DeclaredVars(s);
ensures ReferencedVarsE(e) !! ScopedVarsS(s);
{
  ScopeUpperBound(s);
  assert forall x :: x in ScopedVarsS(s) ==>
          x in ReferencedVarsS(s) || x in DeclaredVars(s);
  GammaDisjoint(ReferencedVarsS(s), DeclaredVars(s), ScopedVarsS(s), ReferencedVarsE(e));
  assert ScopedVarsS(s) !! ReferencedVarsE(e);
}

lemma ScopeDisjointS(s1: Stmt, s2: Stmt)
requires ScopedVarsS(s1) !! ReferencedVarsS(s2);
requires ReferencedVarsS(s1) !! DeclaredVars(s1);
requires ReferencedVarsS(s2) !! DeclaredVars(s2);
requires ReferencedVarsS(s1) !! DeclaredVars(s2);
requires DeclaredVars(s1) !! DeclaredVars(s2);
requires ReferencedVarsS(s1) !! ReferencedVarsS(s2);
ensures ScopedVarsS(s1) !! ScopedVarsS(s2);
{
  ScopeUpperBound(s1);
  assert forall x :: x in ScopedVarsS(s1) ==>
          x in ReferencedVarsS(s1) || x in DeclaredVars(s1);
  GammaDisjoint(ReferencedVarsS(s1), DeclaredVars(s1), ScopedVarsS(s1), DeclaredVars(s2));
  assert ScopedVarsS(s1) !! DeclaredVars(s2);


  ScopeUpperBound(s2);
  assert forall x :: x in ScopedVarsS(s2) ==>
          x in ReferencedVarsS(s2) || x in DeclaredVars(s2);
  GammaDisjoint(ReferencedVarsS(s2), DeclaredVars(s2), ScopedVarsS(s2), ReferencedVarsS(s1));
  assert ScopedVarsS(s2) !! ReferencedVarsS(s1);

  assert ScopedVarsS(s1) !! ReferencedVarsS(s2);
  assert forall x :: x in ScopedVarsS(s2) ==>
          x in ReferencedVarsS(s2) || x in DeclaredVars(s2);
  GammaDisjoint(ReferencedVarsS(s2), DeclaredVars(s2), ScopedVarsS(s2), ScopedVarsS(s1));

  assert ScopedVarsS(s2) !! ScopedVarsS(s1);
}

function method TypeCheckS(g: Gamma, stmt: Stmt): Option<Gamma>
decreases stmt;
ensures TypeCheckS(g, stmt).Some? ==> NoDuplicateDeclarations(stmt);
ensures TypeCheckS(g, stmt).Some? ==> NoDuplicateReferencesS(stmt);
ensures TypeCheckS(g, stmt).Some? ==> NoDuplicateScopeS(stmt);
ensures TypeCheckS(g, stmt).Some? ==> GammaExtendsAdd(ReferencedVarsS(stmt), ScopedVarsS(stmt));
ensures TypeCheckS(g, stmt).Some? ==> DeclaredVars(stmt) !! ReferencedVarsS(stmt);
ensures TypeCheckS(g, stmt).Some? ==> g !! DeclaredVars(stmt);
ensures TypeCheckS(g, stmt).Some? ==> GammaExtends(g, TypeCheckS(g, stmt).val);
ensures TypeCheckS(g, stmt).Some? ==>
        GammaExtendsInv(GammaUnion(g, DeclaredVars(stmt)), TypeCheckS(g, stmt).val);
ensures TypeCheckS(g, stmt).Some? ==> GammaDeclarationsS(g, stmt);
ensures TypeCheckS(g, stmt).Some? ==>
        forall x ::x in ScopedVarsS(stmt) ==> x in TypeCheckS(g, stmt).val && TypeCheckS(g, stmt).val[x].Invalid?;
ensures TypeCheckS(g, stmt).Some? ==>
        forall x ::x in ReferencedVarsS(stmt) ==> x in TypeCheckS(g, stmt).val && TypeCheckS(g, stmt).val[x].Invalid?;
ensures TypeCheckS(g, stmt).Some? ==> TypeCheckS(g, stmt).val ==
        GammaUnion(GammaUnion(g, DeclaredVars(stmt)),
                   ScopedVarsS(stmt));
ensures TypeCheckS(g, stmt).Some? ==> GammaExtendsInv(
        GammaUnion(GammaUnion(g, DeclaredVars(stmt)),
                   ReferencedVarsS(stmt)),
        TypeCheckS(g, stmt).val);
ensures TypeCheckS(g, stmt).Some? ==>
        GammaExtendsInv(g, GammaUnion(g, ReferencedVarsS(stmt)));
ensures TypeCheckS(g, stmt).Some? ==>
        GammaExtends(g, GammaUnion(g, ScopedVarsS(stmt)));
ensures TypeCheckS(g, stmt).Some? ==>
        GammaExtends(g, GammaUnion(g, DeclaredVars(stmt)));
ensures TypeCheckS(g, stmt).Some? && stmt.VarDecl? ==>
        TypeCheckE(g, stmt.vinit).Type? && TypeCheckE(g, stmt.vinit).typ == stmt.vtype;
ensures TypeCheckS(g, stmt).Some? && stmt.If? ==>
        TypeCheckE(g, stmt.cond).Type? &&
        TypeCheckE(g, stmt.cond).typ == BoolT &&
        TypeCheckS(TypeCheckE(g, stmt.cond).gamma, stmt.the).Some? &&
        TypeCheckS(TypeCheckE(g, stmt.cond).gamma, stmt.els).Some? &&
        ReferencedVarsE(stmt.cond) !! ReferencedVarsS(stmt.the) &&
        ReferencedVarsE(stmt.cond) !! ReferencedVarsS(stmt.els);
ensures TypeCheckS(g, stmt).Some? && stmt.While? ==>
        TypeCheckE(g, stmt.wcond).Type? &&
        TypeCheckE(g, stmt.wcond).typ == BoolT &&
        TypeCheckS(TypeCheckE(g, stmt.wcond).gamma, stmt.wbody).Some? &&
        ReferencedVarsE(stmt.wcond) !! ReferencedVarsS(stmt.wbody) &&
        DeclaredVars(stmt.wbody) !! ReferencedVarsS(stmt.wbody);
ensures TypeCheckS(g, stmt).Some? && stmt.Seq? ==>
        TypeCheckS(g, stmt.s1).Some? &&
        TypeCheckS(TypeCheckS(g, stmt.s1).val, stmt.s2).Some? &&
        g !! DeclaredVars(stmt.s1) &&
        g !! DeclaredVars(stmt.s2) &&
        DeclaredVars(stmt.s1) !! DeclaredVars(stmt.s2) &&
        GammaDeclarationsS(g, stmt.s1) &&
        GammaDeclarationsS(TypeCheckS(g, stmt.s1).val, stmt.s2) &&
        ScopedVarsS(stmt.s1) !! ScopedVarsS(stmt.s2);
{
  ghost var gd := DeclaredVars(stmt);

  match stmt {

    case VarDecl(x, vtype, vinit) =>
      if x in g then
        None
      else
        match TypeCheckE(g, vinit) {
          case Type(g2, vt) =>
            if vt == vtype then (
              assert NoDuplicateDeclarations(stmt);
              assert NoDuplicateReferencesS(stmt);
              assert NoDuplicateScopeS(stmt);
              assert GammaExtendsAdd(ReferencedVarsS(stmt), ScopedVarsS(stmt));
              Some(g2[x := T(vt)])
            ) else None
          case Fail => None
        }

    case If(con, the, els) =>
      match TypeCheckE(g, con) {
        case Type(g2, ct) => if !ct.BoolT? then None else match TypeCheckS(g2, the) {
          case Some(g3) => match TypeCheckS(g2, els) {
            case Some(g4) => (
              assert GammaExtendsInv(GammaUnion(g, gd), GammaJoin(g2, GammaJoin(g3, g4)));
              assert NoDuplicateDeclarations(stmt);
              assert NoDuplicateReferencesS(stmt);

              assert NoDuplicateReferencesE(con);
              assert NoDuplicateScopeS(the);
              assert NoDuplicateScopeS(els);

              ScopeDisjointE(con, the);
              assert ReferencedVarsE(con) !! ScopedVarsS(the);
              ScopeDisjointE(con, els);
              assert ReferencedVarsE(con) !! ScopedVarsS(els);

              assert NoDuplicateScopeS(stmt);
              assert GammaExtendsAdd(ReferencedVarsS(stmt), ScopedVarsS(stmt));

              assert forall x :: x in GammaJoin(GammaJoin(g2, g3), g4) ==>
                x in GammaUnion(GammaUnion(g, DeclaredVars(stmt)), ScopedVarsS(stmt));

              assert forall x ::
                x in GammaUnion(GammaUnion(g, DeclaredVars(stmt)), ScopedVarsS(stmt)) ==>
                x in GammaJoin(GammaJoin(g2, g3), g4);

              assert forall x :: x in GammaJoin(GammaJoin(g2, g3), g4) ==>
                x in GammaUnion(GammaUnion(g, DeclaredVars(stmt)), ScopedVarsS(stmt)) &&
                GammaJoin(GammaJoin(g2, g3), g4)[x] ==
                  GammaUnion(GammaUnion(g, DeclaredVars(stmt)), ScopedVarsS(stmt))[x];

              assert forall x ::
                x in GammaUnion(GammaUnion(g, DeclaredVars(stmt)), ScopedVarsS(stmt)) ==>
                x in GammaJoin(GammaJoin(g2, g3), g4) &&
                GammaJoin(GammaJoin(g2, g3), g4)[x] ==
                  GammaUnion(GammaUnion(g, DeclaredVars(stmt)), ScopedVarsS(stmt))[x];

              assert GammaJoin(GammaJoin(g2, g3), g4) ==
                     GammaUnion(GammaUnion(g, DeclaredVars(stmt)),
                                ScopedVarsS(stmt));

              Some(GammaJoin(GammaJoin(g2, g3), g4))
            )
            case None => None
          }
          case None => None
        }
        case Fail => None
      }

    case While(con, body) =>
      match TypeCheckE(g, con) {
        case Type(g2, ct) => if !ct.BoolT? then None else match TypeCheckS(g2, body) {
          case Some(g3) => match TypeCheckE(g3, con) {
            case Type(g4, ct2) => match TypeCheckS(g4, body) {
              case Some(g5) => (
                /* assert GammaExtendsInv(GammaUnion(g, gd), GammaJoin(g2, g3)); */
                assert NoDuplicateDeclarations(stmt);
                assert NoDuplicateReferencesS(stmt);
                assert NoDuplicateScopeS(stmt);
                assert GammaExtendsAdd(ReferencedVarsS(stmt), ScopedVarsS(stmt));
                Some(GammaJoin(g2, g3))
              )
              case None => None
            }
            case Fail => None
          }
          case None => None
        }
        case Fail => None
      }

    case Seq(s1, s2) =>
      match TypeCheckS(g, s1) {
        case Some(g2) => match TypeCheckS(g2, s2) {
          case Some(g3) => (
            assert GammaExtendsInv(GammaUnion(g, DeclaredVars(s1)), g2);
            assert GammaExtendsInv(GammaUnion(g2, DeclaredVars(s2)), g3);
            assert gd == GammaUnion(DeclaredVars(s1), DeclaredVars(s2));
            assert GammaExtendsInv(GammaUnion(g, gd), g3);

            assert ReferencedVarsS(s1) !! ReferencedVarsS(s2);

            assert g2 == GammaUnion(GammaUnion(g, DeclaredVars(s1)),
                                    ScopedVarsS(s1));

            assert g3 == GammaUnion(GammaUnion(g2, DeclaredVars(s2)),
                                    ScopedVarsS(s2));


            assert g3 == GammaUnion(GammaUnion(GammaUnion(GammaUnion(g,
                                                                     DeclaredVars(s1)),
                                                          ScopedVarsS(s1)),
                                               DeclaredVars(s2)),
                                    ScopedVarsS(s2));

            ScopeDisjointS(s1, s2);
            assert ScopedVarsS(s1) !! ScopedVarsS(s2);
            assert g2 == GammaUnion(GammaUnion(g, DeclaredVars(s1)),
                                    ScopedVarsS(s1));

            assert g3 == GammaUnion(GammaUnion(g2, DeclaredVars(s2)),
                                    ScopedVarsS(s2));

            GammaSeqUnion(g, g2, g3, s1, s2);

            assert g3 == GammaUnion(GammaUnion(g, DeclaredVars(stmt)),
                                    ScopedVarsS(stmt));

            assert NoDuplicateDeclarations(stmt);
            assert NoDuplicateReferencesS(stmt);
            assert NoDuplicateScopeS(stmt);

            assert GammaExtendsAdd(ReferencedVarsS(s1), ScopedVarsS(s1));
            assert GammaExtendsAdd(ReferencedVarsS(s2), ScopedVarsS(s2));

            assert forall x :: x in ReferencedVarsS(stmt) ==> x in ScopedVarsS(stmt);

            assert forall x :: x in ReferencedVarsS(stmt) ==> ReferencedVarsS(stmt)[x].Invalid?;
            assert forall x :: x in ScopedVarsS(stmt) ==> ScopedVarsS(stmt)[x].Invalid?;


            assert forall x :: x in ReferencedVarsS(stmt)
                   ==> x in ScopedVarsS(stmt)
                   && ReferencedVarsS(stmt)[x] == ScopedVarsS(stmt)[x];
            assert GammaExtendsAdd(ReferencedVarsS(stmt), ScopedVarsS(stmt));
            Some(g3)
          )
          case None => None
        }
        case None => None
      }

    case Skip => (
      Some(g)
    )
  }
}

type Sigma = map<string, Value>

function TypeSig(sig: Sigma): Gamma {
  map x | x in sig :: T(TypeCheckV(sig[x]))
}

predicate SigmaExtends(sig1: Sigma, sig2: Sigma) {
  forall x :: x in sig1 ==> x in sig2 && sig1[x] == sig2[x]
}

lemma GammaPreservationE(gamma1: Gamma, gamma2: Gamma, expr: Expr)
decreases expr;
requires GammaDeclarationsE(gamma1, expr);
requires GammaDeclarationsE(gamma2, expr);
requires forall x :: x in ReferencedVarsE(expr) ==> gamma1[x] == gamma2[x];
requires TypeCheckE(gamma1, expr).Type?;
ensures TypeCheckE(gamma2, expr).Type?;
ensures TypeCheckE(gamma1, expr).typ == TypeCheckE(gamma2, expr).typ;
{
  match expr {
    case V(val) => {}
    case Var(x) => {}
    case Add(l, r) => {
      assert TypeCheckE(gamma1, l).Type?;
      var g1: Gamma := TypeCheckE(gamma1, l).gamma;
      GammaPreservationE(gamma1, gamma2, l);
      assert TypeCheckE(gamma2, l).Type?;
      var g2: Gamma := TypeCheckE(gamma2, l).gamma;
      assert TypeCheckE(g1, r).Type?;
      GammaPreservationE(g1, g2, r);
      assert TypeCheckE(g2, r).Type?;
      assert TypeCheckE(gamma2, Add(l, r)).Type?;
    }
    case Eq(l, r) => {
      assert TypeCheckE(gamma1, l).Type?;
      var g1: Gamma := TypeCheckE(gamma1, l).gamma;
      GammaPreservationE(gamma1, gamma2, l);
      assert TypeCheckE(gamma2, l).Type?;
      var g2: Gamma := TypeCheckE(gamma2, l).gamma;
      assert TypeCheckE(g1, r).Type?;
      GammaPreservationE(g1, g2, r);
      assert TypeCheckE(g2, r).Type?;
      assert TypeCheckE(gamma2, Eq(l, r)).Type?;
    }
  }
}

function method EvalE(sig: Sigma, expr: Expr): Expr
requires !expr.V?;
requires TypeCheckE(TypeSig(sig), expr).Type?;

ensures TypeCheckE(TypeSig(sig), EvalE(sig, expr)).Type?;
ensures TypeCheckE(TypeSig(sig), expr).typ ==
        TypeCheckE(TypeSig(sig), EvalE(sig, expr)).typ;
ensures GammaExtendsInv(TypeCheckE(TypeSig(sig), EvalE(sig, expr)).gamma,
                        TypeCheckE(TypeSig(sig), expr).gamma);
{
  ghost var g := TypeSig(sig);

  match expr {

    case Var(x) => (
      assert TypeCheckE(g, V(sig[x])).Type?;
      V(sig[x])
    )

    case Add(l, r) =>
      if !l.V? then (
        ghost var g2 := TypeCheckE(g, l).gamma;

        var l2 := EvalE(sig, l);
        assert TypeCheckE(g, l2).Type?;
        ghost var g3 := TypeCheckE(g, l2).gamma;

        assert ReferencedVarsE(l) !! ReferencedVarsE(r);

        assert GammaDeclarationsE(g2, r);
        assert GammaDeclarationsE(g3, r);
        assert TypeCheckE(g2, r).Type?;
        GammaPreservationE(g2, g3, r);
        assert TypeCheckE(g3, r).Type?;

        assert TypeCheckE(g, Add(l2, r)).Type?;
        Add(l2, r)
      ) else if !r.V? then (
        assert TypeCheckE(g, Add(l, EvalE(sig, r))).Type?;
        Add(l, EvalE(sig, r))
      ) else (
        assert TypeCheckE(g, V(Num(l.val.nval + r.val.nval))).Type?;
        V(Num(l.val.nval + r.val.nval))
      )

    case Eq(l, r) =>
      if !l.V? then (
        ghost var g2 := TypeCheckE(g, l).gamma;

        var l2 := EvalE(sig, l);
        assert TypeCheckE(g, l2).Type?;
        ghost var g3 := TypeCheckE(g, l2).gamma;

        assert ReferencedVarsE(l) !! ReferencedVarsE(r);

        assert GammaDeclarationsE(g2, r);
        assert GammaDeclarationsE(g3, r);
        assert TypeCheckE(g2, r).Type?;
        GammaPreservationE(g2, g3, r);
        assert TypeCheckE(g3, r).Type?;

        assert TypeCheckE(g, Eq(l2, r)).Type?;
        Eq(l2, r)
      ) else if !r.V? then (
        assert TypeCheckE(g, Eq(l, EvalE(sig, r))).Type?;
        Eq(l, EvalE(sig, r))
      ) else if l.val.Num? && r.val.Num? then (
        assert TypeCheckE(g, V(Bool(l.val.nval == r.val.nval))).Type?;
        V(Bool(l.val.nval == r.val.nval))
      ) else (
        assert TypeCheckE(g, V(Bool(l.val.bval == r.val.bval))).Type?;
        V(Bool(l.val.bval == r.val.bval))
      )

  }
}

/* lemma SigmaPreservationE(sigma1: Sigma, sigma2: Sigma, expr: Expr) */
/* requires TypeCheckE(TypeSig(sigma1), expr).Type?; */
/* requires SigmaExtends(sigma1, sigma2); */
/* ensures TypeCheckE(TypeSig(sigma2), expr).Type?; */
/* ensures TypeCheckE(TypeSig(sigma1), expr).typ == TypeCheckE(TypeSig(sigma2), expr).typ; */
/* { */
/*   SigmaGammaExtends(sigma1, sigma2); */
/*   GammaPreservationE(TypeSig(sigma1), TypeSig(sigma2), expr); */
/* } */

/* lemma SigmaPreservation(sig: Sigma, stmt: Stmt) */
/* requires !stmt.Skip?; */
/* requires TypeCheckS(TypeSig(sig), stmt).Some?; */
/* ensures (ghost var (sig2,stmt2) := EvalS(sig, stmt); */
/*          GammaExtends(TypeCheckS(TypeSig(sig), stmt).val, */
/*                       TypeCheckS(TypeSig(sig2), stmt2).val)) */
/* {} */

/* lemma GammaPreservationE(g: Gamma, g2: Gamma, expr: Expr) */
/* decreases expr; */
/* requires GammaExtends(g, g2); */
/* requires TypeCheckE(g, expr).Type?; */
/* ensures TypeCheckE(g2, expr).Type?; */
/* ensures TypeCheckE(g, expr).typ == TypeCheckE(g2, expr).typ; */
/* ensures GammaUnion(g2, TypeCheckE(g, expr).gamma) == TypeCheckE(g2, expr).gamma; */
/* ensures GammaExtends(TypeCheckE(g, expr).gamma, TypeCheckE(g2, expr).gamma); */
/* { */
/*   match expr { */

/*     case V(val) => {} */

/*     case Var(x) => {} */

/*     case Add(l, r) => { */
/*       GammaPreservationE(g, g2, l); */
/*       GammaPreservationE(g, g2, r); */
/*     } */

/*     case Eq(l, r) => { */
/*       GammaPreservationE(g, g2, l); */
/*       GammaPreservationE(g, g2, r); */
/*     } */
/*   } */
/* } */

lemma GammaPreservationS(g: Gamma, g2: Gamma, stmt: Stmt)
decreases stmt;
requires TypeCheckS(g, stmt).Some?;
requires GammaDeclarationsS(g, stmt);
requires GammaDeclarationsS(g2, stmt);
requires g !! DeclaredVars(stmt);
requires g2 !! DeclaredVars(stmt);
requires GammaExtends(g, g2);
ensures TypeCheckS(g2, stmt).Some?;
/* ensures GammaUnion(g2, TypeCheckS(g, stmt).val) == TypeCheckS(g2, stmt).val; */
/* ensures GammaExtends(TypeCheckS(g, stmt).val, TypeCheckS(g2, stmt).val); */
{
  match stmt {

    case VarDecl(x, vtype, vinit) => {
      assert x !in g;
      assert x !in g2;
      GammaPreservationE(g, g2, vinit);
    }

    case If(con, the, els) => {
      assert TypeCheckE(g, con).Type?;
      ghost var g3 := TypeCheckE(g, con).gamma;

      GammaPreservationE(g, g2, con);
      assert TypeCheckE(g2, con).Type?;
      assert TypeCheckE(g2, con).typ.BoolT?;
      ghost var g4 := TypeCheckE(g2, con).gamma;

      assert TypeCheckS(g3, the).Some?;
      GammaPreservationS(g3, g4, the);

      assert TypeCheckS(g3, the).Some?;
      GammaPreservationS(g3, g4, els);
    }

    case While(con, body) => {
      assert TypeCheckE(g, con).Type?;
      GammaPreservationE(g, g2, con);
      assert TypeCheckE(g2, con).Type?;
      assert TypeCheckE(g2, con).typ.BoolT?;
      ghost var g3 := TypeCheckE(g2, con).gamma;
      assert GammaExtends(g, g3);
      GammaPreservationS(g, g3, body);
      assert TypeCheckS(g3, body).Some?;
      ghost var g4 := TypeCheckS(g3, body).val;
      assert GammaExtends(g2, g4);
      assert GammaExtends(g2, GammaJoin(g2, g4));
      GammaPreservationE(g2, GammaJoin(g2, g4), con);
      assert TypeCheckE(GammaJoin(g2, g4), con).Type?;
      assert TypeCheckE(GammaJoin(g2, g4), con).typ.BoolT?;
      ghost var g5 := TypeCheckE(GammaJoin(g2, g4), con).gamma;
      assert GammaExtends(g3, g5);
      assert GammaExtends(g3, GammaJoin(g3, g5));
      GammaPreservationS(g3, GammaJoin(g3, g5), body);
      assert TypeCheckS(GammaJoin(g3, g5), body).Some?;
      assert TypeCheckS(g2, stmt).Some?;
    }

    case Seq(s1, s2) => {
      assert TypeCheckS(g, s1).Some?;
      GammaPreservationS(g, g2, s1);

      assert TypeCheckS(g2, s1).Some?;
      ghost var g3 := TypeCheckS(g2, s1).val;
      assert TypeCheckS(TypeCheckS(g, s1).val, s2).Some?;

      assert GammaExtends(TypeCheckS(g, s1).val, g3);
      assert g !! DeclaredVars(s2);
      assert g2 !! DeclaredVars(s2);

      assert TypeCheckS(g, s1).val !! DeclaredVars(s2);

      assert TypeCheckS(TypeCheckS(g, s1).val, s2).Some?;

      assert g3 !! DeclaredVars(s2);
      GammaPreservationS(TypeCheckS(g, s1).val, g3, s2);
      assert TypeCheckS(g3, s2).Some?;
      assert TypeCheckS(g2, stmt).Some?;
    }

    case Skip => {}

  }
}

function method EvalS(sig: Sigma, stmt: Stmt): (Sigma, Stmt)
decreases stmt;
requires !stmt.Skip?;
requires TypeCheckS(TypeSig(sig), stmt).Some?;

ensures SigmaExtends(sig, EvalS(sig, stmt).0);
/* ensures GammaUnion(TypeSig(sig), DeclaredVars(stmt)) == */
/*         GammaUnion(TypeSig(EvalS(sig, stmt).0), DeclaredVars(EvalS(sig, stmt).1)); */
ensures TypeCheckS(TypeSig(EvalS(sig, stmt).0), EvalS(sig, stmt).1).Some?;
/* ensures GammaExtends(ScopedVars(EvalS(sig, stmt).1), ScopedVars(stmt)); */

/* ensures ExportSigma((sig, stmt)) == ExportSigma(EvalS(sig, stmt)); */

/* TypeSig eSig(EvalS(sig, stmt).0), EvalS(sig, stmt).1) */
/* ExportGamma(TypeSig(EvalS(sig, stmt).0), EvalS(sig, stmt).1) */
/*         == ExportGamma(    ScopedVars(stmt)); */
{
  match stmt {

    case VarDecl(x, vt, vinit) =>
      if !vinit.V? then (
        assert TypeCheckS(TypeSig(sig), VarDecl(x, vt, EvalE(sig, vinit))).Some?;
        /* assert GammaExtends(ScopedVars(VarDecl(x, vt, EvalE(sig, vinit))), ScopedVars(stmt)); */
        (sig, VarDecl(x, vt, EvalE(sig, vinit))))
      else (
        assert TypeCheckS(TypeSig(sig[x := vinit.val]), Skip).Some?;
        /* assert GammaExtends(ScopedVars(Skip), ScopedVars(stmt)); */
        (sig[x := vinit.val], Skip))

    case If(cond, the, els) =>
      if !cond.V? then (
        /* assert TypeCheckS(TypeSig(sig), If(EvalE(sig, cond), the, els)).Some?; */
        /* assert GammaExtends(ScopedVars(If(EvalE(sig, cond), the, els)), ScopedVars(stmt)); */
        (sig, If(EvalE(sig, cond), the, els))
      ) else if cond.val.bval then (
        /* assert TypeCheckS(TypeSig(sig), the).Some?; */
        /* assert GammaExtends(ScopedVars(the), ScopedVars(stmt)); */
        /* (sig, the) */

        if !els.Skip? then (
          (sig, If(cond, the, Skip))
        ) else if the.Skip? then (
          assert TypeCheckS(TypeSig(sig), Skip).Some?;
          (sig, Skip)
        ) else (
          var (sig2, the2) := EvalS(sig, the);
          ghost var g: Gamma := TypeSig(sig);
          ghost var g2: Gamma := TypeSig(sig2);
          ghost var g3: Gamma := TypeCheckE(g, cond).gamma;
          ghost var g4: Gamma := TypeCheckE(g2, cond).gamma;
          assert GammaExtends(g3, g4);
          assert TypeCheckS(g4, the2).Some?;
          assert TypeCheckS(g3, els).Some?;
          assert g4 !! DeclaredVars(els);
          GammaPreservationS(g3, g4, els);
          assert TypeCheckS(TypeSig(sig2), If(cond, the2, els)).Some?;
          /* assert ExportSigma((sig, the)) == ExportSigma((sig2, the2)); */
          /* assert ScopedVarsS(stmt) == ScopedVarsS(If(cond, the2, els)); */
          /* assert ExportSigma((sig, stmt)) == ExportSigma((sig2, If(cond, the2, els))); */
          (sig2, If(cond, the2, els))
        )
      ) else (
        if !the.Skip? then (
          (sig, If(cond, Skip, els))
        ) else if els.Skip? then (
          assert TypeCheckS(TypeSig(sig), Skip).Some?;
          (sig, Skip)
        ) else (
          var (sig2, els2) := EvalS(sig, els);
          ghost var g: Gamma := TypeSig(sig);
          ghost var g2: Gamma := TypeSig(sig2);
          ghost var g3: Gamma := TypeCheckE(g, cond).gamma;
          ghost var g4: Gamma := TypeCheckE(g2, cond).gamma;
          assert GammaExtends(g3, g4);
          assert TypeCheckS(g3, the).Some?;
          assert TypeCheckS(g4, els2).Some?;
          assert g4 !! DeclaredVars(the);
          GammaPreservationS(g3, g4, the);
          assert TypeCheckS(TypeSig(sig2), If(cond, the, els2)).Some?;
          (sig2, If(cond, the, els2))
        )
      )

    case While(cond, body) => (
      assert ScopedVarsS(If(V(Bool(true)), body, Skip)) !! DeclaredVars(If(V(Bool(true)), body, Skip));

      assert TypeCheckE(TypeSig(sig), cond).Type?;
      ghost var g: Gamma := TypeCheckE(TypeSig(sig), cond).gamma;

      assert TypeCheckS(g, Skip).Some?;

      assert TypeCheckS(g, Seq(If(V(Bool(true)), body, Skip),
                   While(cond, body))).Some?;

      assert TypeCheckS(TypeSig(sig), If(cond,
               Seq(If(V(Bool(true)), body, Skip),
                   While(cond, body)), Skip)).Some?;
      assert GammaExtends(ScopedVarsS(If(cond,
               Seq(If(V(Bool(true)), body, Skip),
                   While(cond, body)), Skip)), ScopedVarsS(stmt));
      /* assert ExportSigma((sig, stmt)) == ExportSigma((sig, If(cond, */
      /*          Seq(If(V(Bool(true)), body, Skip), */
      /*              While(cond, body)), Skip))); */
      (sig, If(cond,
               Seq(If(V(Bool(true)), body, Skip),
                   While(cond, body)), Skip))
    )

    case Seq(s1, s2) =>
      if s1.Skip? then (
        assert TypeCheckS(TypeSig(sig), s2).Some?;
        assert GammaExtends(ScopedVarsS(s2), ScopedVarsS(stmt));
        (sig, s2)
      ) else (
        var (sig2, s12) := EvalS(sig, s1);
        ghost var g: Gamma := TypeSig(sig);
        ghost var g2: Gamma := TypeSig(sig2);
        assert GammaExtends(g, g2);

        assert TypeCheckS(g, s1).Some?;
        ghost var g3: Gamma := TypeCheckS(g, s1).val;

        assert g !! DeclaredVars(s1);
        assert GammaExtends(g, g3);
        /* assert GammaExtends(TypeCheckS(g, s1).val, GammaUnion(g, DeclaredVars(s1))); */


        assert TypeCheckS(g2, s12).Some?;
        ghost var g4: Gamma := TypeCheckS(g2, s12).val;

        assert TypeCheckS(g3, s2).Some?;

        assert TypeCheckS(g3, s2).Some?;

        assert GammaExtends(g3, g4);

        /* assert GammaExtends(ExportGamma(g2, s1), GammaUnion(g, ScopedVars(s1))); */

        assert g !! DeclaredVars(s2);
        assert GammaUnion(g, ScopedVarsS(s1)) !! DeclaredVars(s2);

        assert g2 !! DeclaredVars(s2);
        assert TypeCheckS(g3, s2).Some?;
        assert GammaExtends(g3, g4);

        assert g4 !! DeclaredVars(s2);
        GammaPreservationS(g3, g4, s2);

        assert TypeCheckS(g4, s2).Some?;

        assert TypeCheckS(g2, Seq(s12, s2)).Some?;
        assert GammaExtends(ScopedVarsS(Seq(s12, s2)), ScopedVarsS(stmt));
        /* assert ExportSigma((sig, stmt)) == ExportSigma((sig2, Seq(s12, s2))); */
        (sig2, Seq(s12, s2))
      )

  }
}

/* predicate CanStepE(sig: Sigma, expr: Expr) */
/* { */
/*   expr.V? || EvalE(sig, expr).ResE? */
/* } */

/* predicate CanStep(sig: Sigma, stmt: Stmt) */
/* { */
/*   stmt.Skip? || EvalS(sig, stmt).Res? */
/* } */

/* /1* lemma PreservationE(sig: Sigma, expr: Expr) *1/ */
/* /1* requires EvalE(sig, expr).ResE?; *1/ */
/* /1* requires TypeCheckE(TypeSig(sig), expr).Type?; *1/ */
/* /1* ensures TypeCheckE(TypeSig(EvalE(sig, expr).sig), EvalE(sig, expr).expr).Type?; *1/ */
/* /1* ensures TypeCheckE(TypeSig(sig), expr).typ == *1/ */
/* /1*         TypeCheckE(TypeSig(EvalE(sig, expr).sig), EvalE(sig, expr).expr).typ; *1/ */
/* /1* { *1/ */
/* /1*   match expr { *1/ */
/* /1*     case V(val) => { *1/ */
/* /1*     } *1/ */

/* /1*     case Var(x) => { *1/ */
/* /1*     } *1/ */

/* /1*     case Add(l, r) => { *1/ */
/* /1*       /2* PreservationE(sig, l); *2/ *1/ */
/* /1*       /2* PreservationE(sig, r); *2/ *1/ */
/* /1*     } *1/ */

/* /1*     case Eq(l, r) => { *1/ */
/* /1*     } *1/ */
/* /1*   } *1/ */
/* /1* } *1/ */

/* method Run(prog: Stmt) { */
/*   var t: Option<Gamma> := TypeCheckS(map[], prog); */
/*   if t.None? { */
/*     print "Type error!\n"; */
/*   } else { */
/*     print "Type checking succesful.\nEvaluating...\n"; */
/*     var n:nat := 0; */
/*     var env: Sigma := map[]; */
/*     var s: Stmt := prog; */
/*     while n < 100000 && !s.Skip? */
/*     { */
/*       var res: EvalSRes := EvalS(env, s); */
/*       if res.Halt? { */
/*         print "This should never happen."; */
/*         s := Skip; */
/*       } else { */
/*         s := res.stmt; */
/*         env := res.env; */
/*       } */
/*       n := n + 1; */
/*     } */
/*     print "Ran "; */
/*     print n; */
/*     print " steps.\n\nFinal environment:\n"; */
/*     print env; */
/*     print "\n"; */
/*   } */
/* } */

