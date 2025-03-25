// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Good luck!
//
// END-TODO(Name)

datatype BYTree = BlueLeaf
                | YellowLeaf
                | Node(left: BYTree, right: BYTree)

// BEGIN-TODO(Extra)
// Space for extra functions and lemmas (optional)
// END-TODO(Extra)

function Mirror(t: BYTree): BYTree
{
// BEGIN-TODO(Mirror)
    match t
    case BlueLeaf => BlueLeaf
    case YellowLeaf => YellowLeaf
    case Node(left, right) => Node(Mirror(right), Mirror(left))
// END-TODO(Mirror)
}

