---- MODULE philosophers_cm ----

(*
In 1984, K. Mani Chandy and J. Misra[5] proposed a different solution to the dining philosophers problem to allow for arbitrary agents (numbered P1, ..., Pn)
to contend for an arbitrary number of resources, unlike Dijkstra's solution. It is also completely distributed and requires no central authority after initialization.
However, it violates the requirement that "the philosophers do not speak to each other" (due to the request messages).

- For every pair of philosophers contending for a resource, create a fork and give it to the philosopher with the lower ID (n for agent Pn).
Each fork can either be dirty or clean. Initially, all forks are dirty.(i+1)%N

- When a philosopher wants to use a set of resources (i.e. eat), said philosopher must obtain the forks from their contending neighbors.
For all such forks the philosopher does not have, they send a request message.

- When a philosopher with a fork receives a request message, they keep the fork if it is clean, but give it up when it is dirty.
If the philosopher sends the fork over, they clean the fork before doing so.

- After a philosopher is done eating, all their forks become dirty. If another philosopher had previously requested one of the forks,
the philosopher that has just finished eating cleans the fork and sends it.
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

Clean == "C"
Dirty == "D"

Left  == "L"
Right == "R"

VARIABLES
    state,
    forks_state,
    forks_cleanliness

TypeInvariant ==
    [](/\ state \in [ Philos -> { Hungry, Thinking, Eating }]
    /\ forks_state  \in [Forks -> {Left,  Right}]
    /\ forks_cleanliness \in [ Forks -> { Clean, Dirty}])

Safety ==
    (\A i \in {j \in Philos: state[j] = Eating}:
        \/ ~state[left(i)] = Eating
        \/ ~state[right(i)] = Eating)

Liveness == [](\A i \in Philos : state[i] = Hungry => <>(state[i] = Eating))

GlobalLiveness == []((\E i \in Philos: state[i] = Hungry) => <>(\E j \in Philos: state[j] = Eating))

----------------------------------------------------------------

Init ==
    /\ state = [ i \in Philos |-> Thinking ]
    /\ forks_state = [[i \in Forks |-> Left ] EXCEPT ![0] = Right]
    /\ forks_cleanliness = [ i \in Forks |-> Dirty ]

ask(i) ==
    /\ state[i] = Thinking
    /\ state' = [ state EXCEPT ![i] = Hungry ]
    /\ UNCHANGED <<forks_state, forks_cleanliness>>

eat(i) ==
    /\ state[i] = Hungry
    /\ state[left(i)] /= Eating
    /\ state[right(i)] /= Eating
    /\ forks_state[left(i)] = Right
    /\ forks_state[i] = Left
    /\ state' = [ state EXCEPT ![i] = Eating ]
    /\ UNCHANGED <<forks_state, forks_cleanliness>>

think(i) ==
    /\ state[i] = Eating
    /\ forks_state' = [ forks_state EXCEPT
        ![left(i)] = IF state[left(i)]  = Hungry THEN Left  ELSE forks_state[left(i)],
        ![i]       = IF state[right(i)] = Hungry THEN Right ELSE forks_state[i]]
    /\ forks_cleanliness' = [ forks_cleanliness EXCEPT
        ![left(i)] = IF state[left(i)] = Hungry  THEN Clean ELSE Dirty,
        ![i]       = IF state[right(i)] = Hungry THEN Clean ELSE Dirty]
    /\ state' = [ state EXCEPT ![i] = Thinking ]

request_left_fork(i) ==
    /\ state[i] = Hungry
    /\ forks_state[left(i)] /= Right
    /\ forks_cleanliness[left(i)] = Dirty
    /\ forks_state'       = [ forks_state       EXCEPT ![left(i)] = Right ]
    /\ forks_cleanliness' = [ forks_cleanliness EXCEPT ![left(i)] = Clean ]
    /\ UNCHANGED state

request_right_fork(i) ==
    /\ state[i] = Hungry
    /\ forks_state[i] /= Left
    /\ forks_cleanliness[i] = Dirty
    /\ forks_state'       = [ forks_state       EXCEPT ![i] = Left ]
    /\ forks_cleanliness' = [ forks_cleanliness EXCEPT ![i]  = Clean ]
    /\ UNCHANGED state

Next ==
  \E i \in Philos : \/ ask(i)
                    \/ eat(i)
                    \/ think(i)
                    \/ request_left_fork(i)
                    \/ request_right_fork(i)

Fairness ==
    \A i \in Philos :
        /\ WF_<<state, forks_state, forks_cleanliness>>(eat(i))
        /\ WF_<<state, forks_state, forks_cleanliness>>(think(i))
        /\ WF_<<state, forks_state, forks_cleanliness>>(request_left_fork(i))
        /\ WF_<<state, forks_state, forks_cleanliness>>(request_right_fork(i))

Spec ==
  /\ Init
  /\ [] [ Next ]_<<state, forks_state, forks_cleanliness>>
  /\ Fairness


====