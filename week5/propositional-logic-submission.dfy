// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Good luck!
//
// END-TODO(Name)

datatype Expr =
  True 
  | False
  | Var(s: string)
  | Not(arg: Expr) 
  | And(left: Expr, right: Expr)
  | Or(left: Expr, right: Expr)
  | Implies(left: Expr, right: Expr)

// BEGIN-TODO(Extra)
function CountNodes(x: Expr): nat{
  match x
  case True => 1
  case False => 1
  case Var(s) => 1
  case Not(arg) => 1 + CountNodes(arg)
  case And(left, right) => 1 + CountNodes(left) + CountNodes(right)
  case Or(left, right) => 1 + CountNodes(left) + CountNodes(right)
  case Implies(left, right) => 1 + CountNodes(left) + CountNodes(right)
}
// END-TODO(Extra)

predicate Eval(x: Expr, env: map<string, bool>)
{
// BEGIN-TODO(Eval)
match x
case True => true
case False => false
case Var(s) => s in env && env[s]
case Not(arg) => !Eval(arg, env)
case And(left, right) => Eval(left, env) && Eval(right, env)
case Or(left, right) => Eval(left, env) || Eval(right, env)
case Implies(left, right) => Eval(left, env) ==> Eval(right, env)
// END-TODO(Eval)
}

method TestEval()
{
  var env := map["a" := true, "b" := false, "c" := true];
  assert Eval(And(True, True), env) == true;
  assert Eval(Implies(Var("a"), False), env) == false;
}

function Simplify(x: Expr): Expr
// BEGIN-TODO(Simplify)
decreases CountNodes(x)
{
  match x {
  case True => True
  case False => False
  case Var(s) => Var(s)
  
  case Not(arg) => 
    var simplifiedArg := Simplify(arg);
    match simplifiedArg {
      case True => False
      case False => True
      case Not(arg1) => arg1
      case _ => Not(simplifiedArg)
    }

  case And(left, right) =>
    var simplifiedLeft := Simplify(left);
    var simplifiedRight := Simplify(right);
    match simplifiedLeft {
    case False => False
    case True => simplifiedRight
    case _ =>
      match simplifiedRight {
      case False => False
      case True => simplifiedLeft
      case _ => if simplifiedLeft == simplifiedRight then simplifiedLeft else And(simplifiedLeft, simplifiedRight)
      }
    }
  case Or(left, right) =>
    var simplifiedLeft := Simplify(left);
    var simplifiedRight := Simplify(right);
    match simplifiedLeft {
    case True => True
    case False => simplifiedRight
    case _ =>
      match simplifiedRight {
      case True => True
      case False => simplifiedLeft
      case _ => if simplifiedLeft == simplifiedRight then simplifiedLeft else Or(simplifiedLeft, simplifiedRight)
      }
    }

  case Implies(left, right) =>
    var simplifiedLeft := Simplify(left);
    var simplifiedRight := Simplify(right);
    match simplifiedLeft {
    case True => simplifiedRight
    case False => True
    case _ =>
      match simplifiedRight {
      case True => True
      case False => Not(simplifiedLeft)
      case _ => Implies(simplifiedLeft, simplifiedRight)
      }
    }
  }
}

//Lemma
lemma SimplifyLemma(x: Expr, env: map<string, bool>)
  ensures Eval(x, env) == Eval(Simplify(x), env)
  decreases CountNodes(x)
{
  match x {
  case True => 
    assert Eval(x, env) == Eval(Simplify(x), env);
  case False =>
    assert Eval(x, env) == Eval(Simplify(x), env);
  case Var(s) =>
    assert Eval(x, env) == Eval(Simplify(x), env);
  case Not(arg) =>
    SimplifyLemma(arg, env);
    assert Eval(x, env) == Eval(Simplify(x), env);
  case And(left, right) => {
    SimplifyLemma(left, env);
    SimplifyLemma(right, env);
    assert Eval(x, env) == Eval(Simplify(x), env);
  }
  case Or(left, right) => {
    SimplifyLemma(left, env);
    SimplifyLemma(right, env);
    assert Eval(x, env) == Eval(Simplify(x), env);
  }
  case Implies(left, right) => {
    SimplifyLemma(left, env);
    SimplifyLemma(right, env);
    assert Eval(x, env) == Eval(Simplify(x), env);
  }
  }
}
// END-TODO(Simplify)

method TestSimplify()
{
// BEGIN-TODO(TestSimplify)
// Insert your test cases for the `Simplify` function.
var env := map["a" := true, "b" := false, "c" := true];
assert Simplify(Not(Var("a"))) == Not(Var("a"));
// True Inversion
assert Simplify(Not(True)) == False;
// False Inversion
assert Simplify(Not(False)) == True;
// Double Negation
assert Simplify(Not(Not(Var("a")))) == Var("a");
// Idempotence
assert Simplify(And(Var("a"), Var("a"))) == Var("a");
assert Simplify(Or(Var("a"), Var("a"))) == Var("a");
// True - Elim
assert Simplify(And(Var("a"), True)) == Var("a");
assert Simplify(Or(Var("a"), True)) == True;
assert Simplify(And(True, Var("a"))) == Var("a");
assert Simplify(Or(True, Var("a"))) == True;
// False - Elim
assert Simplify(And(Var("a"), False)) == False;
assert Simplify(Or(Var("a"), False)) == Var("a");
assert Simplify(And(False, Var("a"))) == False;
assert Simplify(Or(False, Var("a"))) == Var("a");
// Implication cases
assert Simplify(Implies(True, Var("a"))) == Var("a");
assert Simplify(Implies(False, Var("a"))) == True;
assert Simplify(Implies(Var("a"), True)) == True;
assert Simplify(Implies(Var("a"), False)) == Not(Var("a"));
// Complex Cases
assert Simplify(And(Or(Var("a"), False), Not(Not(Var("b"))))) == And(Var("a"), Var("b"));
assert Simplify(Or(And(Var("a"), True), And(False, Var("b")))) == Var("a");
// END-TODO(TestSimplify)
}
