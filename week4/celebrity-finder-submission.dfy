// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group <Group number>
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
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
   (forall p' | p' in people && p' != p :: knows(p', p)) && (forall p' | p' in people && p' != p :: !knows(p, p'))
// END-TODO(IsCelebrity)
  }    

  method FindCelebrity(people: People) returns (result: Person)
// BEGIN-TODO(FindCelebrity)
    requires exists p | p in people :: isCelebrity(people, p)
    ensures isCelebrity(people, result)
    {
      var C := people;
      var a: Person;
      var b: Person;
      a :| a in C;
      C := C - {a};
      while |C| > 0 
        invariant isCelebrity(people, a) || exists p | p in C :: isCelebrity(people, p)
        invariant C <= people
        invariant a !in C && a in people
      {
        b :| b in C;
        C := C - {b};
        assert isCelebrity(people, a) || exists p | p in C + {b} :: isCelebrity(people, p);
        if (knows(a, b)) {
          assert !isCelebrity(people, a);
          assert exists p | p in C + {b} :: isCelebrity(people, p);
          a := b;
          // a was not a celebrity, but it knows b, so either b is a celebrity, or there must be another celebrity in C
          assert isCelebrity(people, a) || exists p | p in C :: isCelebrity(people, p);
        } else {
          assert !isCelebrity(people, b);
          // b was not a celebrity, so he can safely be removed from C without affecting the presence of a celebrity
          assert isCelebrity(people, a) || exists p | p in C :: isCelebrity(people, p);
        }
      }
      assert isCelebrity(people, a);
      result := a;
    }
// END-TODO(FindCelebrity)

}
