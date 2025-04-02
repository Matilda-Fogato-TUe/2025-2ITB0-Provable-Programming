// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group <Group number>
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
//
// Good luck!
//
// END-TODO(Name)

/* == Book exercise 16.7 ==
 * As written, Tokenizer holds on to the given string forever. Change the design
 * to make it possible to prune the storage through a method that throws away
 * the prefix of the source string that has already been processed.
 * Specifically, make source a ghost and declare a mutable field suffix with the
 * invariant suffix == source[m..], where m is a new field. For example, you can
 * introduce fields m and j such that m + j == n, in which case you can declare
 * n as ghost as well. Modify the implementation of Read accordingly. */

datatype Category = Identifier | Number | Operator | Whitespace | Error | End

predicate Is(ch: char, cat: Category)
    requires cat != End
    decreases cat == Error
{
    match cat
        case Whitespace => ch in " \t\r\n"
        case Identifier => 'A' <= ch <= 'Z' || 'a' <= ch <= 'z'
        case Number => '0' <= ch <= '9'
        case Operator => ch in "+-*/%!=><~^&|"
        case Error => !Is(ch, Identifier) && !Is(ch, Number) &&
                        !Is(ch, Operator) && !Is(ch, Whitespace)
}

// BEGIN-TODO(Extra)
// Space for extra functions and lemmas (optional)
// END-TODO(Extra)

class Tokenizer {
// BEGIN-TODO(Attributes)
// Add the class fields here. Part of it may come from 16.6-blueprint.dfy,
// possibly with changes
// END-TODO(Attributes)

    ghost predicate Valid()
        reads this
    {
// BEGIN-TODO(Invariant)
// Add the (changed) class invariant here (use 16.6-blueprint.dfy)
// END-TODO(Invariant)    
    }

    constructor (s: string)
        ensures Valid() && source == s && n == 0
    {
// BEGIN-TODO(Constructor)
// Add the (changed) constructor body here
// END-TODO(Constructor)
    }

    method Read() returns (cat: Category, ghost p: nat, token: string)
        requires Valid()
        modifies this
        ensures cat == End || cat == Error || Valid()
        ensures cat != Whitespace
        ensures old(n) <= p <= n <= |source|
        ensures cat == End <==> p == |source|
        ensures cat == End || cat == Error <==> p == n
        ensures forall i :: old(n) <= i < p ==> Is(source[i], Whitespace)
        ensures forall i :: p <= i < n ==> Is(source[i], cat)
        ensures p < n ==> n == |source| || !Is(source[n], cat)
        ensures token == source[p..n]
    {
// BEGIN-TODO(Read)
// Add the body of the function Read here
// END-TODO(Read)
    }

    method Prune()
        requires Valid()
        modifies this
        ensures Valid() && source == old(source[m..]) == suffix
    {
// BEGIN-TODO(Prune)
// Add the body of the Prune method here
// END-TODO(Prune)
    }

// BEGIN-TODO(Methods)
// Space for extra methods (optional)
// END-TODO(Methods)
}
