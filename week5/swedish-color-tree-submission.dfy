// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Good luck!
//
// END-TODO(Name)

datatype ColoredTree = Leaf(Color)
                     | Node(ColoredTree, ColoredTree)

datatype Color = Blue | Yellow | Green | Red

predicate IsSwedishFlagColor(c : Color)
{
  c.Blue? || c.Yellow?
}

// BEGIN-TODO(Extra)
// Space for extra functions and lemmas (optional)
// END-TODO(Extra)

predicate IsSwedishColoredTree(t: ColoredTree)
{
  // BEGIN-TODO(IsSwedishColorTree)
  // Define a predicate on colored trees that determines whether all leaves have colors that are part of the Swedish flag.
  match t
  {
    case Leaf(c) => IsSwedishFlagColor(c)
    case Node(left, right) => IsSwedishColoredTree(left) && IsSwedishColoredTree(right)
  }

  // END-TODO(IsSwedishColorTree)
}
