// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Good luck!
//
// END-TODO(Name)

module CelebrityFinderModule
{
  type Person = nat
  type People = set<Person>

  predicate knows(p: Person, q: Person)

  predicate isCelebrity(people: People, p: Person)
  {
    // BEGIN-TODO(IsCelebrity)
    // Implement the `isCelebrity` predicate according to the instructions.
    p in people &&
    (forall q: Person :: (q in people && p != q) ==> knows(q, p)) &&
    (forall q: Person :: (q in people && p != q) ==> (!knows(p, q)))
    // END-TODO(IsCelebrity)
  }

  method FindCelebrity(people: People) returns (result: Person)
    // BEGIN-TODO(FindCelebrity)
    // Implement the `FindCelebrity` method according to the instructions.
    requires people != {}
    requires (exists c: Person :: c in people && isCelebrity(people, c))
    ensures isCelebrity(people, result)
  {
    // Initialize a set C with all people in the community
    var C := people;
    // Initialize a candidate celebrity by removing an arbitrary person from C
    var a: Person :| a in C;
    C := C - {a};
    // Initialize an arbitrary person b
    var b: Person;
    // While C is not empty:
    // Remove an arbitrary person b from C
    // Check if a knows b
    // If a knows b, update the candidate celebrity to b
    // When the loop terminates, a is the celebrity
    while C != {}
      invariant isCelebrity(people, a) || (exists p: Person :: p in C && isCelebrity(people, p))
      invariant a in people && a !in C
      invariant C <= people
      decreases |C|
    {
      b :| b in C;  // Remove an arbitrary person b from C
      C := C - {b};
      if knows(a, b) {
        a := b;  // Update the candidate celebrity to b
      }
    }
    result := a;
  }
  // END-TODO(FindCelebrity)

}
