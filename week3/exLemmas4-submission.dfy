// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Go get 'em!
//
// END-TODO(Name)

function Mult(x: nat, y: nat): nat {
  if y == 0 then 0 else x + Mult(x, y - 1)
}

lemma MultCommutative(x: nat, y: nat)
  decreases x + y
  ensures Mult(x, y) == Mult(y, x)
{
  // BEGIN-TODO(MultComm)
  // Write a proof for the commutativity of multiplication based on the
  // specification given in `Mult`.
  if x == 0 || y == 0 {
    // Base case
    assert Mult(x, y) == 0;
    assert Mult(y, x) == 0;
  } else {
    // Inductive step
    calc {
      Mult(x, y);
    ==
      x + Mult(x, y - 1); // Apply definition of Mult
    ==
      {
        MultCommutative(x, y - 1); // Induction hypothesis
        assert Mult(x, y - 1) == Mult(y - 1, x);
      }
      x + Mult(y - 1, x); // Apply induction hypothesis
    ==
      x + (y - 1) + Mult(y - 1, x - 1); // Apply definition of Mult
    ==
      y + Mult(y, x -1); // Simplify
    ==
      Mult(y, x); // Apply definition of Mult
    }
  }
  // END-TODO(MultComm)
}