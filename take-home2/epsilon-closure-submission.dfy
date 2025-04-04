// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group 36
// Matilda Fogato: 1656376
// Jip Melle Verkoulen: 1836587
//
// Good luck!
//
// END-TODO(Name)

abstract module NFAModule
{
  // The type State represents a state in an automaton.
  type State(00,==,!new)

  // The type Symbol represents a symbol in the alphabet of an automaton.
  type Symbol(00,==,!new)

  // The type Word represents a sequence of symbols.
  // It models strings over the alphabet in the context of automata.
  type Word = seq<Symbol>

  // The type Alphabet represents a set of symbols.
  // It defines the allowable symbols for transitions in an automaton.
  type Alphabet = set<Symbol>

  // The constant epsilon represents the special symbol ε that is used in Non-deterministic Finite Automata.
  const epsilon: Symbol

  // Checks if the states of path `p` are restricted to the set `Q`.
  ghost predicate is_restricted_path(p: seq<State>, Q: set<State>)
  {
    forall q | q in p :: q in Q
  }

  // Determines whether `r` is an epsilon-path in the NFA `N`.
  // An epsilon-path is a sequence of states where each consecutive pair of states is connected 
  // by an epsilon (ε) transition, and all states in the path belong to the state set `N.Q`.
  ghost predicate is_epsilon_path(N: NFA, r: seq<State>)
  {
    var n := |r| - 1;
    |r| > 0 &&
    is_restricted_path(r, N.Q) &&
    (forall i | 0 <= i < n :: ((r[i], epsilon) in N.delta.Keys && r[i + 1] in N.delta[(r[i], epsilon)]))
  }

  // A simple path is a path that does not revisit any vertex (state), except possibly the
  // starting and ending vertices in the case of a cycle.
  ghost predicate is_simple_path(p: seq<State>)
    requires |p| > 0
  {
    if p[0] == p[|p|-1] then // p is a cycle
      forall i, j | 0 <= i < j < |p|-1 :: p[i] != p[j]
    else
      forall i, j | 0 <= i < j < |p| :: p[i] != p[j]
  }

  // The type NFA_unchecked models a Non-deterministic Finite Automaton (NFA). It is termed 'unchecked' because it may represent an invalid NFA.
  // An NFA is defined by:
  // - Q: A set of states.
  // - Sigma: An alphabet (set of symbols).
  // - delta: A transition map that maps a pair (state, symbol) to a set of states.
  // - q0: An initial state.
  // - F: A set of accepting (final) states.
  datatype NFA_unchecked = NFA_(Q: set<State>, Sigma: Alphabet, delta: map<(State, Symbol), set<State>>, q0: State, F: set<State>)

  // The type NFA represents a valid NFA that satisfies the predicate is_nfa.
  // It is defined as a subset of NFA_unchecked where the validity conditions are met.
  // The ghost witness 'nfa_witness' ensures that there exists at least one valid NFA.
  type NFA = N: NFA_unchecked | is_nfa(N) ghost witness nfa_witness()

  // This ghost function provides an example witness for an NFA_unchecked that satisfies the predicate is_nfa.
  ghost function nfa_witness(): NFA_unchecked
    ensures is_nfa(nfa_witness())
  {
    ghost var q0: State :| true;  // Choose an arbitrary state.
    NFA_({q0}, {}, map[], q0, {}) // Return an NFA with one state, no alphabet, and no transitions.
  }

  // The predicate is_nfa checks if a given NFA_unchecked satisfies the conditions of a valid NFA.
  // Validity conditions:
  // - The initial state q0 must be in the set of states Q.
  // - The set of accepting states F must be a subset of Q.
  // - Epsilon (empty string symbol) must not be in the alphabet Sigma.
  // - Every transition (q, a) in the delta map must satisfy:
  //     * q is a valid state in Q.
  //     * a is either a symbol in Sigma or epsilon.
  //     * The resulting set of states from delta must all be in Q.
  ghost predicate is_nfa(N: NFA_unchecked)
  {
    N.q0 in N.Q &&
    N.F <= N.Q &&
    epsilon !in N.Sigma &&
    forall q, a | (q, a) in N.delta.Keys ::
    (
      q in N.Q &&
      a in N.Sigma + {epsilon} &&
      N.delta[(q, a)] <= N.Q
    )
  }

  // Checks if the state `q` is reachable from the state `p` in the NFA `N` via epsilon (ε) transitions.
  ghost predicate is_epsilon_reachable(N: NFA, p: State, q: State)
  {
    exists r: seq<State> ::
      is_epsilon_path(N, r) &&
      r[0] == p &&
      r[|r|-1] == q
  }

  // Returns the set of epsilon-successor states of a single state `q` in the NFA `N`.
  // An epsilon-successor is any state reachable from `q` via an epsilon (ε) transition.
  ghost function epsilon_successors(N: NFA, q: State): set<State>
  {
    if ((q, epsilon) in N.delta.Keys) then N.delta[(q, epsilon)] else {}
  }

  // Returns the set of epsilon-successor states of a set of states `Q` in the NFA `N`.
  // The result includes all states reachable via an epsilon (ε) transition from any state in `Q`.
  ghost function E(N: NFA, Q: set<State>): set<State>
  {
    set q1, q2: State | q1 in Q && (q1, epsilon) in N.delta.Keys && q2 in N.delta[(q1, epsilon)] :: q2
  }

  // Returns the epsilon-closure of a single state `q` in the NFA `N`.
  // The epsilon-closure is the set of all states reachable from `q` via zero or more epsilon (ε) transitions.
  ghost function epsilon_closure(N: NFA, q: State): set<State>
    ensures epsilon_closure(N, q) <= N.Q
  {
    set q1: State | q1 in N.Q && is_epsilon_reachable(N, q, q1) :: q1
  }

  // Returns the epsilon-closure of a set of states `Q` in the NFA `N`.
  // The epsilon-closure is the set of all states reachable from any state in `Q` via zero or more epsilon (ε) transitions.
  ghost function EC(N: NFA, Q: set<State>): set<State>
    requires Q <= N.Q
    ensures EC(N, Q) <= N.Q
  {
    set q1, q2: State | q1 in Q && q2 in N.Q && is_epsilon_reachable(N, q1, q2) :: q2
  }

  // Convert from one-state definition to set definition
  lemma EpsilonClosureLemma(N: NFA, q: State)
    requires q in N.Q
    ensures epsilon_closure(N, q) == EC(N, {q})
  { }
}

abstract module NFAAlgorithmsModule refines NFAModule
{
  // Proves that if there exists an epsilon-path between two states in an NFA `N`, then there exists
  // a simple epsilon-path between the same two states in `N`.
  lemma SimpleEpsilonPathLemma(N: NFA, r: seq<State>)
    requires is_epsilon_path(N, r)
    ensures exists r1: seq<State> :: is_epsilon_path(N, r1) && is_simple_path(r1) && r1[0] == r[0] && r1[|r1|-1] == r[|r|-1]
    // BEGIN-TODO(SimpleEpsilonLemma)
    // Prove this lemma by adding a body.
  {
    if is_simple_path(r) {
      // r is already simple
    } else {
      // since r is not simple, there exists i, j such that r[i] == r[j]
      // and 0 <= i < j < |r| - 1
      var i, j :| 0 <= i < j < |r| && r[i] == r[j];
      // remove the cycle by concatenating the prefix of r up to i with the suffix of r from j
      var rprime := r[..i] + r[j..];
      // endpoints are preserved
      assert rprime[0] == r[0];
      assert rprime[|rprime|-1] == r[|r|-1];

      assert is_epsilon_path(N, rprime)
      by {
        // rprime is a subsequence of r
        assert is_restricted_path(rprime, N.Q);
        assert |rprime| > 0;
        // all transitions in rprime are also in r
        assert forall k | 0 <= k < |rprime| - 1 :: ((rprime[k], epsilon) in N.delta.Keys && rprime[k + 1] in N.delta[(rprime[k], epsilon)]);
      }
      // we removed at least one state, so |rprime| < |r|
      assert |rprime| < |r|;

      // by induction hypothesis, there exists a simple epsilon-path r1 with the same endpoints as rprime
      SimpleEpsilonPathLemma(N, rprime);
    }
  }
  // END-TODO(SimpleEpsilonLemma)

  // BEGIN-TODO(Extra)
  // Space for extra functions and lemmas (optional)
  lemma DiscoveredUnionSubset(N: NFA, q: State, discovered_old: set<State>, Q1: set<State>)
    requires discovered_old <= epsilon_closure(N, q)
    requires forall r :: r in Q1 ==> r in epsilon_closure(N, q)
    ensures discovered_old + Q1 <= epsilon_closure(N, q)
  {
    // The union of two subsets of epsilon_closure(N, q) is itself a subset of epsilon_closure(N, q).
  }

  lemma EpsilonTransitionPreservesClosure(N: NFA, q: State, p: State, r: State)
    requires p in epsilon_closure(N, q)
    requires (p, epsilon) in N.delta
    requires r in N.delta[(p, epsilon)]
    ensures r in epsilon_closure(N, q)
  {
    // Let the path r1 be the sequence of states from q to p.
    var r1 :| is_epsilon_path(N, r1) && r1[0] == q && r1[|r1|-1] == p;
    // The path r1 is an epsilon-path because it is a sequence of states connected by epsilon-transitions.

    // Concatenate r1 with the state [r] to form a new path r2.
    var r2 := r1 + [r];

    // The path r2 is an epsilon-path because it consists of the original epsilon-transitions from q to p,
    // followed by the epsilon-transition from p to r.
    // Therefore, r is in epsilon_closure(N, q) because there exists an epsilon-path from q to r.
    assert r2[0] == q;
    assert r2[|r2|-1] == r;
    assert |r2| > 0;
    assert forall i | 0 <= i < |r2| - 1 :: ((r2[i], epsilon) in N.delta.Keys && r2[i + 1] in N.delta[(r2[i], epsilon)]);
    assert is_epsilon_path(N, r2);
    assert r in epsilon_closure(N, q);

  }

  lemma SuffixOfEpsilonPathIsEpsilonPath(N: NFA, path: seq<State>, i:nat)
    requires is_epsilon_path(N, path)
    requires 0 <= i < |path|
    ensures is_epsilon_path(N, path[i..])
  {
    assert is_restricted_path(path[i..], N.Q);
    assert |path[i..]| > 0;
  }

  // END-TODO(Extra)

  method nfa_epsilon_closure(N: NFA, q: State) returns (discovered: set<State>)
    // BEGIN-TODO(RemoveDecreases)
    // END-TODO(RemoveDecreases)
    requires q in N.Q
    ensures discovered == epsilon_closure(N, q)
  {
    discovered := {q};
    var todo := {q};

    // BEGIN-TODO(EntryCondition)
    assert todo <= discovered;
    assert q in discovered;
    assert q in epsilon_closure(N, q)
    by {
      var path := [q];
      assert |path| > 0;
      assert is_restricted_path(path, N.Q);
      assert is_epsilon_path(N, path);
    }
    assert todo == {q};
    assert todo <= epsilon_closure(N, q);
    assert discovered <= epsilon_closure(N, q);
    // States not in 'discovered' but still in epsilon_closure(N, q) must come from a state in 'todo',
    // so they fall under EC(N, todo). This justifies the subset relation:
    assert epsilon_closure(N, q) <= discovered + EC(N, todo);
    assert E(N, discovered - todo) <= discovered;
    // END-TODO(EntryCondition)

    while |todo| > 0
      // BEGIN-TODO(Termination)
      // Replace `*` with an appropriate decreases clause to ensure termination.
      decreases (|epsilon_closure(N, q)| - |discovered|, |todo|)
      invariant q in discovered
      // END-TODO(Termination)
      invariant todo <= discovered <= epsilon_closure(N, q)
      invariant epsilon_closure(N, q) <= discovered + EC(N, todo)
      invariant E(N, discovered - todo) <= discovered
    {
      var p :| p in todo;
      todo := todo - {p};

      if ((p, epsilon) in N.delta)
      {
        var Q1 := N.delta[(p, epsilon)] - discovered;

        // BEGIN-TODO(Invariant1)
        if Q1 == {} {
          assert todo <= todo - {p} + Q1;
          assert discovered == discovered + Q1;
        } else {
          assert |Q1| > 0;
          assert |discovered| < |discovered + Q1|;
        }
        var discovered_old := discovered;
        // For every r in Q1, prove it is in epsilon_closure(N, q)
        forall r | r in Q1 {
          EpsilonTransitionPreservesClosure(N, q, p, r);
        }
        assert forall r :: r in Q1 ==> r in epsilon_closure(N, q);
        assert Q1 <= epsilon_closure(N, q);
        // END-TODO(Invariant1)

        discovered := discovered + Q1;
        todo := todo + Q1;

        // BEGIN-TODO(Maintenance)
        if Q1 != {} {
          assert |discovered| > |discovered_old|;
        }

        DiscoveredUnionSubset(N, q, discovered_old, Q1);
        assert todo <= discovered;
        assert discovered <= epsilon_closure(N, q)
        by {
          DiscoveredUnionSubset(N, q, discovered_old, Q1);
        }

        assert epsilon_closure(N, q) <= discovered + EC(N, todo)
        by {
          forall r | r in epsilon_closure(N, q)
            ensures r in discovered + EC(N, todo)
          {
            if r in discovered {
              // r is already discovered
            } else {
              // There's an epsilon path from q to r
              var path :| is_epsilon_path(N, path) && path[0] == q && path[|path|-1] == r;
              assert q in discovered;
              assert path[0] in discovered;
              // Find the first undiscovered state in path
              var i := 0;
              while i < |path| && path[i] in discovered
                invariant 0 <= i <= |path|
                invariant forall j :: 0 <= j < i ==> path[j] in discovered
              {
                i := i + 1;
              }

              assert i > 0; // path[0] = q is discovered
              if path[i-1] in todo {
                // Then r is in EC(N, todo)
                SuffixOfEpsilonPathIsEpsilonPath(N, path, i-1);
                assert r in EC(N, todo);
              } else {
                // Contradiction: if path[i-1] is outside todo,
                // it must be in discovered - todo whose epsilon successors are discovered
                assert false;
              }
            }
          }
        }

        assert E(N, discovered - todo) <= discovered;
        // END-TODO(Maintenance)
      }
    }

    // BEGIN-TODO(Result)
    assert todo == {};
    assert epsilon_closure(N, q) <= discovered;
    assert discovered == epsilon_closure(N, q);
    // END-TODO(Result)
  }
}
