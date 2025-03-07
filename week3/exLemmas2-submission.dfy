// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Go get 'em!
//
// END-TODO(Name)

lemma ExA(x: int, y: int)
  // BEGIN-TODO(PostA)
  // Add as a postcondition the equality we mean to prove.
  ensures 5*x - 3 * (y + x) == 2*x - 3*y
  // END-TODO(PostA)
{
  calc ==
  {
    // BEGIN-TODO(CalcA)
    // Add at least three expressions for this calculation, starting with the
    // left-hand side of the goal equation and ending with the right-hand side.
    //
    // Note that this calc statement has `==` as a fixed comparison operator.
    5*x - 3 * (y + x);
  ==
    5*x - 3*y - 3*x;
  ==
    (5-3)*x - 3*y;
  ==
    2*x - 3*y;
    // END-TODO(CalcA)
  }
}


lemma ExB(x: int, y: int)
  // BEGIN-TODO(PostB)
  // Add as a postcondition the equality we mean to prove.
  ensures 2 * (x + 4*y + 7) - 10 == 2*x + 8*y + 4
  // END-TODO(PostB)
{
  calc ==
  {
    // BEGIN-TODO(CalcB)
    // Add at least three expressions for this calculation, starting with the
    // left-hand side of the goal equation and ending with the right-hand side.
    //
    // Note that this calc statement has `==` as a fixed comparison operator.
    2 * (x + 4*y + 7) - 10;
  ==
    2*x + 8*y + 14 - 10;
  ==
    2*x + 8*y + 4;

    // END-TODO(CalcB)
  }
}


lemma ExC(x: int)
  // BEGIN-TODO(PostC)
  // Add as a postcondition the equality we mean to prove.
  ensures 7*x + 5 < (x + 3) * (x + 4)
  // END-TODO(PostC)
{
  calc
  {
     // BEGIN-TODO(CalcC)
     // Add at least three expressions for this calculation, starting with the
     // left-hand side of the goal equation and ending with the right-hand side.
     //
     // Note that this calc statement does not have a fixed comparison operator.
     7 * x + 5;
  <
     7 * x + 12;
     // x * x is non-negative
  <= x * x + 7 * x + 12;
  ==
     (x + 3) * (x + 4);
     // END-TODO(CalcC)
  }
}
