// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Good luck!
//
// END-TODO(Name)

/* == Book exercise 16.6 ==
 * Extend the Tokenizer example to treat the first character of a token
 * differently. Specifically, replace predicate Is with two predicates:
 * IsStart(ch, cat) says whether or not character ch is a legal initial
 * character of category cat, and IsFollow(ch, cat) says whether or not ch is a
 * legal non-initial character of cat. Use these to allow Identifier to start
 * with a letter and to continue with any letters and digits. Then, update the
 * specification and implementation of method Read(). */

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

// BEGIN-TODO(MethodsAndMore)
predicate IsStart(ch: char, cat: Category)
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

predicate IsFollow(ch: char, cat: Category)
    requires cat != End
    decreases cat == Error
{
    match cat
        case Whitespace => ch in " \t\r\n"
        case Identifier => 'A' <= ch <= 'Z' || 'a' <= ch <= 'z' || '0' <= ch <= '9'
        case Number => '0' <= ch <= '9'
        case Operator => ch in "+-*/%!=><~^&|"
        case Error => !Is(ch, Identifier) && !Is(ch, Number) &&
                        !Is(ch, Operator) && !Is(ch, Whitespace)
}
// END-TODO(MethodsAndMore)

class Tokenizer {
    const source: string
    var n: nat

    ghost predicate Valid()
        reads this
    {
        n <= |source|
    }

    constructor (s: string)
        ensures Valid() && source == s && n == 0
    {
        source, n := s, 0;
    }

    method Read() returns (cat: Category, ghost p: nat, token: string)
        requires Valid()
        modifies this
// BEGIN-TODO(Read)
        ensures cat == End || cat == Error || Valid()
        ensures cat != Whitespace
        ensures old(n) <= p <= n <= |source|
        ensures cat == End <==> p == |source|
        ensures cat == End || cat == Error <==> p == n
        ensures forall i :: old(n) <= i < p ==> IsStart(source[i], Whitespace)
        ensures forall i :: p <= i < n ==> IsFollow(source[i], cat)
        ensures p < n ==> n == |source| || !IsFollow(source[n], cat)
        ensures token == source[p..n]
    {
        // skip whitespace
        while n != |source| && IsStart(source[n], Whitespace)
            invariant old(n) <= n <= |source|
            invariant forall i :: old(n) <= i < n ==> IsStart(source[i], Whitespace)
        {
            n := n + 1;
        }

        p := n;

        // determine syntactic category
        if n == |source| {
            return End, p, "";
        } else if IsStart(source[n], Identifier) {
            cat := Identifier;
        } else if IsStart(source[n], Number) {
            cat := Number;
        } else if IsStart(source[n], Operator) {
            cat := Operator;
        } else {
            return Error, p, "";
        }

        // read token
        var start := n;
        n := n + 1;

        while n != |source| && IsFollow(source[n], cat)
            invariant p <= n <= |source|
            invariant forall i :: p < i < n ==> IsFollow(source[i], cat)
        {
            n := n + 1;
        }

        token := source[start..n];
    }
// END-TODO(Read)
}
