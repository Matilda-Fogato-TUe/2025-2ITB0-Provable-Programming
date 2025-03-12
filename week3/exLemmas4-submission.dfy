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
  if x == y {
        assert Mult(x,y) == Mult(y, x);
    } else if x == 0 {
        MultCommutative(x, y - 1);
    } else if y == 0 {
        MultCommutative(y, x - 1);
    } else {
        calc {
            Mult(x, y);
            == // Def. Mult
            x + Mult(x, y - 1);
            == {MultCommutative(x, y - 1);}
            x + Mult(y - 1, x);
            == // Def. Mult
            x + y - 1 + Mult(y - 1, x - 1);
            == {MultCommutative(y - 1, x - 1);}
            y + x - 1 + Mult(x - 1, y - 1);
            == // Def. Mult
            y + Mult(x - 1, y);
            == {MultCommutative(x - 1, y);}
            y + Mult(y, x - 1);
            == // Def. Mult
            Mult(y, x);
        }
    }
  // END-TODO(MultComm)
}