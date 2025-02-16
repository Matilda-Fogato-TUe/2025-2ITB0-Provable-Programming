// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
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
// Add your derivation here.
// END-TODO(ExerciseB)


// BEGIN-TODO(ExerciseD)
// Add your changed signature here.
// END-TODO(ExerciseD)

// Good luck!!
