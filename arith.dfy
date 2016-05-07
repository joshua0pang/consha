datatype Option<T> = None | Some(val: T)

datatype Value = Num(n: int)
              | Bool(b: bool)
datatype Expr = V(Value)
              | Add(leftA: Expr, rightA: Expr)
              | Eq(leftE: Expr, rightE: Expr)
              | If(cond: Expr, the: Expr, els: Expr)

datatype Type = NumT
              | BoolT

function method TypeCheck(expr: Expr): Option<Type>
ensures TypeCheck(expr).Some? && expr.Add? ==> TypeCheck(expr.leftA).Some? && TypeCheck(expr.leftA).val.NumT?;
{
  match expr {
    case V(val) => match val {
      case Num(_) => Some(NumT)
      case Bool(_) => Some(BoolT)
    }
    case Add(l, r) => match TypeCheck(l) {
      case Some(lt) => if !lt.NumT? then None else match TypeCheck(r) {
        case Some(rt) => if !rt.NumT? then None else Some(NumT)
        case None => None
      }
      case None => None
    }
    case Eq(l, r) => match TypeCheck(l) {
      case Some(lt) => match TypeCheck(r) {
        case Some(rt) => if lt == rt then Some(BoolT) else None
        case None => None
      }
      case None => None
    }
    case If(con, the, els) => match TypeCheck(con) {
      case Some(ct) => if !ct.BoolT? then None else match TypeCheck(the) {
        case Some(thet) => match TypeCheck(els) {
          case Some(elst) => if thet == elst then Some(thet) else None
          case None => None
        }
        case None => None
      }
      case None => None
    }
  }
}

function method Eval(expr: Expr): Option<Value> {
  match expr {
    case V(val) => Some(val)
    case Add(l, r) => match Eval(l) {
      case Some(lv) => match lv {
        case Num(ln) => match Eval(r) {
          case Some(rv) => match rv {
            case Num(rn) => Some(Num(ln + rn))
            case Bool(rb) => None
          }
          case None => None
        }
        case Bool(lb) => None
      }
      case None => None
    }
    case Eq(l, r) => match Eval(l) {
      case Some(lv) => match Eval(r) {
        case Some(rv) => Some(Bool(lv == rv))
        case None => None
      }
      case None => None
    }
    case If(con, the, els) => match Eval(con) {
      case Some(cv) => match cv {
        case Bool(cb) => if cb then Eval(the) else Eval(els)
        case Num(cn) => None
      }
      case None => None
    }
  }
}

lemma Correctness(expr: Expr)
  requires TypeCheck(expr).Some?
  ensures Eval(expr).Some?;
  ensures TypeCheck(expr).val.NumT? == Eval(expr).val.Num?;
  ensures TypeCheck(expr).val.BoolT? == Eval(expr).val.Bool?;
{
  match expr {
    case V(val) => { }
    case Add(l, r) => {
      assert(TypeCheck(l).Some? && TypeCheck(l).val.NumT?);
      Correctness(l);
      assert(Eval(l).Some? && Eval(l).val.Num?);
      assert(TypeCheck(r).Some? && TypeCheck(r).val.NumT?);
      Correctness(r);
      assert(Eval(r).Some? && Eval(r).val.Num?);
      assert(Eval(expr).Some? && Eval(expr).val.Num?);
    }
    case Eq(l, r) => {
      assert(TypeCheck(l).Some?);
      assert(TypeCheck(r).Some?);
      assert(TypeCheck(l).val == TypeCheck(r).val);
      Correctness(l);
      Correctness(r);
      assert(TypeCheck(expr).val.BoolT? ==> Eval(expr).val.Bool?);
      assert(TypeCheck(expr).val.NumT? ==> Eval(expr).val.Num?);
    }
    case If(con, the, els) => {
      assert(TypeCheck(con).Some? && TypeCheck(con).val.BoolT?);
      Correctness(con);
      assert(Eval(con).Some? && Eval(con).val.Bool?);
      assert(TypeCheck(the).Some?);
      assert(TypeCheck(els).Some?);
      assert(TypeCheck(the).val == TypeCheck(els).val == TypeCheck(expr).val);
      Correctness(the);
      Correctness(els);
      assert(TypeCheck(expr).val.BoolT? ==> Eval(expr).val.Bool?);
      assert(TypeCheck(expr).val.NumT? ==> Eval(expr).val.Num?);
    }
  }
}

method Run(prog: Expr) {
  var t: Option<Type> := TypeCheck(prog); // Some(NumT)
  if t.None? {
    print "Type error!\n";
  } else {
    print "Type checking succesful.\nEvaluating...\n";
    var res: Option<Value> := Eval(prog);
    assert t.Some?;
    Correctness(prog);
    assert res.Some?;
    print res.val; // Some(Num(3))
  }
}
