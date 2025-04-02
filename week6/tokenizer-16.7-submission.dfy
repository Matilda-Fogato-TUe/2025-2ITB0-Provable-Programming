// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
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
    ghost const source : string
    ghost var n : int
    var m : nat // number of characters pruned
    var j : nat // n but for the new array
    var suffix : string
// END-TODO(Attributes)

    ghost predicate Valid()
        reads this
    {
// BEGIN-TODO(Invariant)
        //0 <= m <= n <= |source| && suffix == source[m..] && m + j == n && 0 <= j <= n && j <= |suffix|
        0 <= m <= |source| && 0 <= j <= |suffix| && n <= |source| && suffix == source[m..] && m + j == n && source == source[..m] + suffix
// END-TODO(Invariant)    
    }

    constructor (s: string)
        ensures Valid() && source == s && n == 0
    {
// BEGIN-TODO(Constructor)
    source, suffix := s, s;
    n, m, j := 0, 0, 0;
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
        // skip whitespace
        while j != |suffix| && Is(suffix[j], Whitespace)
            invariant old(j) <= j <= |suffix|
            invariant forall i :: old(j) <= i < j ==> Is(suffix[i], Whitespace)
            invariant n == m + j && m <= |source|
            invariant suffix == source[m..]
            invariant old(m) == m
            // invariant old(n) <= j + m
            // invariant old(n) <= n <= |source|
            // invariant forall i :: old(n)<= i < n ==> Is(source[i], Whitespace)
            {
                j := j + 1;
                n := n + 1;
            }
        
        p := j + m;

        // determine syntactic category
        if j == |suffix| {
            return End, p, "";
        } else if Is(suffix[j], Identifier) {
            cat := Identifier;
        } else if Is(suffix[j], Number) {
            cat := Number;
        } else if Is(suffix[j], Operator) {
            cat := Operator;
        } else {
            return Error, p, "";
        }
    	
        // read token
        var start := j;
        n := n + 1;
        j := j + 1;
        //assert m <= |source|;
        assert old(n) <= p;
        while j != |suffix| && Is(suffix[j], cat)
            invariant p - m <= j <= |suffix|
            invariant forall i :: start <= i < j ==> Is(suffix[i], cat)
            invariant n == m + j
            // invariant old(n) <= p
            invariant p == start + m
            invariant suffix == source[m..]

        {
            n := n + 1;
            j := j + 1;
        }

        token := suffix[start..j];
        assert suffix[start..j] == source[p..n];
// END-TODO(Read)
    }

    method Prune()
        requires Valid()
        modifies this
        ensures Valid() && source == old(source[m..]) == suffix
    {
// BEGIN-TODO(Prune)
// Add the body of the Prune method here
    suffix := suffix[j..];
    m := m + j;
    j := 0;
// END-TODO(Prune)
    }

// BEGIN-TODO(Methods)
// Space for extra methods (optional)
// END-TODO(Methods)
}
