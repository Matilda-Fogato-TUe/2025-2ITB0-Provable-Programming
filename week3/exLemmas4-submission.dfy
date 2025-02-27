// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group <Group number>
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
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
// END-TODO(MultComm)
}