---------------- MODULE philosophers ----------------
(* 
IMPORTANT: This attempted solution fails because it allows the system to reach a deadlock state,
in which no progress is possible. This is a state in which each philosopher has picked up the fork to the left,
and is waiting for the fork to the right to become available. With the given instructions, this state can be reached,
and when it is reached, each philosopher will eternally wait for another (the one to the right) to release a fork.

Look at the Chandy/Misra solution for a solution that override this deadlock.
*)

EXTENDS Naturals

CONSTANT N

Philos == 0..N-1
Forks == 0..N-1

left(i) == (i+1)%N       \* get the philo or fork at the left of n°i
right(i) == (i+N-1)%N     \* get the philo or fork at the right of n°i

Hungry == "H"
Thinking == "T"
Eating == "E"
Unhold == N

VARIABLES
    state,
    forks_state

TypeInvariant ==
    [](/\ state \in [ Philos -> { Hungry, Thinking, Eating }]
        /\ forks_state \in [ Forks -> 0..N])

Safety == [](\A x \in Philos: \A y \in Philos \ { x }: ~(state[x] = Eating /\ state[y] = Eating))

Liveness == [](\A i \in Philos : state[i] = Hungry => <>(state[i] = Eating))

GlobalLiveness == []((\E i \in Philos: state[i] = Hungry) => <>(\E j \in Philos: state[j] = Eating))

----------------------------------------------------------------

Init ==
    /\ state = [ i \in Philos |-> Thinking ]
    /\ forks_state = [ i \in Forks |-> Unhold ]

ask(i) ==
    /\ state[i] = Thinking
    /\ state' = [ state EXCEPT ![i] = Hungry ]
    /\ UNCHANGED forks_state

eat(i) ==
    /\ state[i] = Hungry
    /\ state[left(i)] /= Eating
    /\ state[right(i)] /= Eating
    /\ forks_state[left(i)] = i
    /\ forks_state[right(i)] = i
    /\ state' = [ state EXCEPT ![i] = Eating ]
    /\ UNCHANGED forks_state

think(i) ==
    /\ state[i] = Eating
    /\ forks_state' = [ forks_state EXCEPT
        ![left(i)] = Unhold,
        ![right(i)] = Unhold]
    /\ state' = [ state EXCEPT ![i] = Thinking ]

request_left_fork(i) ==
    /\ state[i] = Hungry
    /\ forks_state[left(i)] = Unhold
    /\ forks_state' = [ forks_state EXCEPT ![left(i)] = i ]
    /\ UNCHANGED state

request_right_fork(i) ==
    /\ state[i] = Hungry
    /\ forks_state[right(i)] = Unhold
    /\ forks_state' = [ forks_state EXCEPT ![right(i)] = i ]
    /\ UNCHANGED state

Next ==
  \E i \in Philos : \/ ask(i)
                    \/ eat(i)
                    \/ think(i)
                    \/ request_left_fork(i)
                    \/ request_right_fork(i)

Fairness ==
    \A i \in Philos :
        /\ WF_<<state, forks_state>>(eat(i))
        /\ WF_<<state, forks_state>>(think(i))
        /\ WF_<<state, forks_state>>(request_left_fork(i))
        /\ WF_<<state, forks_state>>(request_right_fork(i))

Spec ==
  /\ Init
  /\ [] [ Next ]_<<state, forks_state>>
  /\ Fairness

================================
