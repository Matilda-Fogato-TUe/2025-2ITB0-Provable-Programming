// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Jip Melle Verkoulen: 1836587
// Matilda Fogato: 1656376
// Group number 36
// END-TODO(Name)



/* 
 * Given is the formula
 * (∃x[P (x) : Q(x)] ∧ ∀y [Q(y) : R(y)]) ⇒ ∃z [P (z) : R(z)] */

/* (a) Prove this formula by giving a derivation in the proof system of the
 * course Logic and Set Theory. */

/* (b) Write this derivation in Dafny, following the same steps. */

/* (c) The formula also verifies in Dafny without intermediate steps.
 * Try this. */

/* (d) Consider the signature given for this exercise' lemma. Consider how this
 * signature can be changed without changing its meaning, by changing
 * pre- and postconditions.  */

lemma Ex6bis<T>(P: T -> bool, Q: T -> bool, R: T -> bool)
  ensures ((exists x:T | P(x) :: Q(x)) && (forall y:T | Q(y) :: R(y)))
          ==>  exists z:T | P(z) :: R(z)

// BEGIN-TODO(ExerciseB)
// Add your derivation here.
{
  if ((exists x: T | P(x) :: Q(x)) && (forall y: T | Q(y) :: R(y))) {
    forall y: T | Q(y) ensures R(y) {
      ghost var x: T :| P(x) && Q(x);
      assert P(x) && Q(x);
      assert R(x);
    }
    assert exists z: T | P(z) :: R(z);
  }
  assert ((exists x: T | P(x) :: Q(x)) && (forall y: T | Q(y) :: R(y))) ==> exists z: T | P(z) :: R(z);
}

// END-TODO(ExerciseB)

// BEGIN-TODO(ExerciseD)
lemma Ex6bis2<T>(P: T -> bool, Q: T -> bool, R: T -> bool)
  requires (exists x: T | P(x) :: Q(x)) && (forall y: T | Q(y) :: R(y))
  ensures exists z: T | P(z) :: R(z) 
{
  assert exists x: T | P(x) :: Q(x);
  assert forall y: T | Q(y) :: R(y);
  ghost var X: T :| P(X) && Q(X);
  assert P(X);
  assert Q(X);
  assert R(X);
  assert exists z: T | P(z) :: R(z);
}
// END-TODO(ExerciseD)
