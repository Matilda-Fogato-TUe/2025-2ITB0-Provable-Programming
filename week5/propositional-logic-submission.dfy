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
// Space for extra functions and lemmas (optional)
lemma SimplifyLemma(x: Expr, env: map<string, bool>)
  ensures Eval(x, env) == Eval(Simplify(x), env)
{
  match x
  case True => assert Eval(True, env) == Eval(Simplify(True), env);
  case False => assert Eval(False, env) == Eval(Simplify(False), env);
  case Var(s) => assert Eval(Var(s), env) == Eval(Simplify(Var(s)), env);
  case Not(arg) => SimplifyLemma(arg, env);
  case And(left, right) => SimplifyLemma(left, env);
  SimplifyLemma(right, env);
  case Or(left, right) => SimplifyLemma(left, env);
  SimplifyLemma(right, env);

  case Implies(left, right) => SimplifyLemma(left, env);
  SimplifyLemma(right, env);
}
// END-TODO(Extra)

predicate Eval(x: Expr, env: map<string, bool>)
{
  // BEGIN-TODO(Eval)
  // Implement the `Eval` predicate according to the instructions.
  match x
  case True => true
  case False => false
  case Var(s) => if s in env.Keys then env[s] else false
  case Not(arg) => !Eval(arg, env)
  case And(left, right) => Eval(left, env) && Eval(right, env)
  case Or(left, right) => Eval(left, env) || Eval(right, env)
  case Implies(left, right) => !Eval(left, env) || Eval(right, env)
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
  // Implement the `Simplify` function according to the instructions.
{
  match x
  case True => True
  case False => False
  case Var(s) => Var(s)

  case Not(arg) =>
    var sa := Simplify(arg);
    (match sa
     // Inversion rules
     case True => False
     case False => True
     // Double negation
     case Not(a) => a
     // Otherwise
     case _ => Not(sa))

  case And(left, right) =>
    var sl := Simplify(left);
    var sr := Simplify(right);
    (match (sl, sr)
     case (False, _) => False
     case (_, False) => False
     case (True, r) => r
     case (l, True) => l
     // Idempotence for AND
     case (l, r) =>
       if l == r then l
       else And(l, r))

  case Or(left, right) =>
    var sl := Simplify(left);
    var sr := Simplify(right);
    (match (sl, sr)
     case (True, _) => True
     case (_, True) => True
     case (False, r) => r
     case (l, False) => l
     // Idempotence for OR
     case (l, r) =>
       if l == r then l
       else Or(l, r))

  case Implies(left, right) =>
    var sl := Simplify(left);
    var sr := Simplify(right);
    (match (sl, sr)
     // If left is False or right is True
     case (False, _) => True
     case (_, True) => True
     // If left is True => result is right (sr)
     case (True, r) => r
     // If right is False => Not(left)
     case (l, False) => Not(l)
     // Otherwise, keep the implies
     case _ => Implies(sl, sr))

}
// END-TODO(Simplify)

method TestSimplify()
{
  // BEGIN-TODO(TestSimplify)

  // Check basic behavior on True/False
  assert Simplify(True) == True;
  assert Simplify(False) == False;

  // Check basic Not (inversion rules and double negation)
  assert Simplify(Not(True)) == False;
  assert Simplify(Not(False)) == True;
  assert Simplify(Not(Not(Var("x")))) == Var("x");

  // Check AND with True/False
  assert Simplify(And(True, Var("p"))) == Var("p");
  assert Simplify(And(Var("p"), True)) == Var("p");
  assert Simplify(And(False, Var("p"))) == False;
  assert Simplify(And(Var("p"), False)) == False;
  // Idempotence
  assert Simplify(And(Var("p"), Var("p"))) == Var("p");

  // Check OR with True/False
  assert Simplify(Or(True, Var("q"))) == True;
  assert Simplify(Or(Var("q"), True)) == True;
  assert Simplify(Or(False, Var("q"))) == Var("q");
  assert Simplify(Or(Var("q"), False)) == Var("q");

  // Idempotence
  assert Simplify(Or(Var("q"), Var("q"))) == Var("q");

  // Check Implies with True/False
  assert Simplify(Implies(False, Var("r"))) == True;
  assert Simplify(Implies(Var("r"), True)) == True;
  assert Simplify(Implies(True, False)) == False;
  assert Simplify(Implies(True, Var("x"))) == Var("x");

  // Check combinations
  assert Simplify(Not(And(True, False))) == True;
  assert Simplify(Implies(And(False, Var("p")), Or(True, Var("p")))) == True;
  // END-TODO(TestSimplify)
}
