// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Jip Melle Verkoulen: 1836587
// Matilda Fogato: 1656376
// Group number 36
// END-TODO(Name)



/* 
 * Given is the formula
 * ∀x[P (x) : Q(x) ∧ R(x)] ⇒ ∀y [¬Q(y) : ¬P (y)] */

/* (a) Prove this formula by giving a derivation in the proof system of the
 * course Logic and Set Theory. */

/* (b) Write this derivation in Dafny, following the same steps. */

/* (c) The formula also verifies in Dafny without intermediate steps.
 * Try this. */

/* (d) Consider the signature given for this exercise' lemma. Consider how this
 * signature can be changed without changing its meaning, by changing
 * pre- and postconditions.  */

lemma Ex5bis<T>(P: T -> bool, Q: T -> bool, R: T -> bool)
  ensures (forall x: T | P(x) :: (Q(x) && R(x))) ==> forall y: T | !Q(y) :: !P(y)
// BEGIN-TODO(ExerciseB)
{
  if (forall x: T | P(x) :: (Q(x) && R(x))) {
    forall y: T | !Q(y) ensures !P(y) {
      if (P(y)) {
        assert Q(y) && R(y);
        assert Q(y);
        assert false;
      }
      assert !P(y);
    }
    assert (forall y: T | !Q(y) :: !P(y));
  }
  assert (forall x: T | P(x) :: Q(x) && R(x)) ==> forall y: T | !Q(y) :: !P(y);
}
// END-TODO(ExerciseB)


// BEGIN-TODO(ExerciseD)
// Add your changed signature here.
lemma Ex5bisbis<T>(P: T -> bool, Q: T -> bool, R: T -> bool)
  requires (forall x: T | P(x) :: (Q(x) && R(x)))
  ensures forall y: T | !Q(y) :: !P(y)
{
  forall y: T | !Q(y) ensures !P(y) {
    if (P(y)) {
      assert Q(y) && R(y);
      assert Q(y);
      assert false;
    }
    assert !P(y);
  }
  assert (forall y: T | !Q(y) :: !P(y));
}
// END-TODO(ExerciseD)

// Good luck!!
