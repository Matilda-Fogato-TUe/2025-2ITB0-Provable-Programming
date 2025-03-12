// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Go get 'em!
//
// END-TODO(Name)

method terminate_x_y(N: nat)
{
  var x, y := 0, 0;
  while x != 0 || y != N
// BEGIN-TODO(Termination)
    decreases N - y, x
    invariant 0 <= y <= N
// END-TODO(Termination)
  {
    if
    {
      case x != 0 => x := x - 1;
      case y != N => x, y := N, y + 1;
    }
  }
}
