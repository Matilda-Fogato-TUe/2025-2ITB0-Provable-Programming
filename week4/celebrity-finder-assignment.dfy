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
// END-TODO(IsCelebrity)
  }    

  method FindCelebrity(people: People) returns (result: Person)
// BEGIN-TODO(FindCelebrity)
// Implement the `FindCelebrity` method according to the instructions.
// END-TODO(FindCelebrity)

}
