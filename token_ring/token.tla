---------------- MODULE token ----------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

ASSUME N \in Nat /\ N > 1

Process == 0..N-1

WantsInCs == "W"
NonCritical == "N"
InCs == "I"

VARIABLES
  state,
  token,
  last

TypeInvariant ==
   [] (/\ state \in [ Process -> {WantsInCs,NonCritical,InCs} ]
       /\ token \in Process)


\* Safety == [](\E x \in Process: \A y \in Process: state[y] = InCs => x = y) other version with \E!
Safety == [](\A x \in Process: \A y \in Process \ { x }: ~(state[x] = InCs /\ state[y] = InCs))

(*
    Whenever any process requests to enter its critical section,
    it will eventually be permitted to do so.
*)
Liveness == [](\A i \in Process : state[i] = WantsInCs => <>(state[i] = InCs))

\* Communication protocols
TokenForAll == []<>(\A i \in Process: token = i)

Sanity == [](\A i \in Process : state[i] = InCs => token = i)

----------------------------------------------------------------

Init ==
    /\ state = [ i \in Process |-> NonCritical ]
    /\ token \in Process
    /\ last = N

ask(i) ==
    /\ state[i] = NonCritical
    /\ state' = [ state EXCEPT ![i] = WantsInCs ]
    /\ UNCHANGED <<token, last>>

enter(i) ==
    /\ i /= last
    /\ state[i] = WantsInCs
    /\ token = i
    /\ state' = [ state EXCEPT ![i] = InCs ]
    /\ last' = i
    /\ UNCHANGED token

exit(i) ==
    /\ state[i] = InCs
    /\ state' = [ state EXCEPT ![i] = NonCritical ]
    /\ UNCHANGED <<token, last>>

move(i) ==
    /\ token = i
    /\ state[i] # InCs
    /\ token' = (i+1)%N
    /\ UNCHANGED <<state, last>>

Next ==
    \E i \in Process :
        \/ ask(i)
        \/ enter(i)
        \/ exit(i)
        \/ move(i)

Fairness == \A i \in Process :
    /\ WF_<<state,token>> (enter(i))
    /\ WF_<<state,token>> (exit(i))
    /\ WF_<<state,token>> (move(i))

Spec ==
    /\ Init
    /\ [] [ Next ]_<<state,token, last>>
    /\ Fairness

================
