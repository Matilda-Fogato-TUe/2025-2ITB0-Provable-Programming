// BEGIN-TODO(Name)
// Please, before you do anything else, add your names here:
// Group <Group number>
// <Full name 1>: <Student number 1>
// <Full name 2>: <Student number 2>
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
// END-TODO(SimpleEpsilonLemma)

// BEGIN-TODO(Extra)
// Space for extra functions and lemmas (optional)
// END-TODO(Extra)

  method nfa_epsilon_closure(N: NFA, q: State) returns (discovered: set<State>)
// BEGIN-TODO(RemoveDecreases)
// After adding a decreases clause to the while loop below, this `decreases *` clause should be removed.
    decreases *
// END-TODO(RemoveDecreases)
    requires q in N.Q
    ensures discovered == epsilon_closure(N, q)
  {
    discovered := {q};
    var todo := {q};

// BEGIN-TODO(EntryCondition)
// Eliminate these assume statements.
    assume todo <= discovered <= epsilon_closure(N, q);
    assume epsilon_closure(N, q) <= discovered + EC(N, todo);
    assume E(N, discovered - todo) <= discovered;
// END-TODO(EntryCondition)

    while |todo| > 0
// BEGIN-TODO(Termination)
// Replace `*` with an appropriate decreases clause to ensure termination.
      decreases *
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
// Eliminate this assume statement.
        assume Q1 <= epsilon_closure(N, q);
// END-TODO(Invariant1)

        discovered := discovered + Q1;
        todo := todo + Q1;

// BEGIN-TODO(Maintenance)
// Eliminate these assume statements.
    assume todo <= discovered <= epsilon_closure(N, q);
    assume epsilon_closure(N, q) <= discovered + EC(N, todo);
    assume E(N, discovered - todo) <= discovered;
// END-TODO(Maintenance)
      }
    }

// BEGIN-TODO(Result)
// Eliminate this assume statement.
    assume discovered == epsilon_closure(N, q);
// END-TODO(Result)
  }
}
