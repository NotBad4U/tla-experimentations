(*
    In the missionaries and cannibals problem, three missionaries and
    three cannibals must cross a river using a boat which can carry
    at most two people, under the constraint that, for both banks, if
    there are missionaries present on the bank, they cannot be
    outnumbered by cannibals (if they were, the cannibals would eat
    the missionaries). The boat cannot cross the river by itself with
    no people on board. And, in some variations, one of the cannibals
    has only one arm and cannot row.
*)

---- MODULE canibale ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Cannibals, Missionaries

Banks == {"L", "R"}

VARIABLES leftBank, rightBank, bank, boat

Entities == Cannibals \union Missionaries

GetMissionaries(S) == S \intersect Missionaries
GetCannibals(S) == S \intersect Cannibals

OtherBank(b) == IF b = "L" THEN "R" ELSE "L"

TypeInvariant ==
    [] (/\ leftBank \subseteq Entities
        /\ rightBank \subseteq Entities
        /\ boat \subseteq Entities
        /\ bank \in Banks
        /\ leftBank \intersect rightBank = {}
        /\ leftBank \union rightBank = Entities)

Init ==
    /\ leftBank = Entities
    /\ rightBank = {}
    /\ boat = {} \* used only for inspect
    /\ bank = "L"

Guard(s) ==
    \/ s \subseteq Cannibals
    \/ Cardinality(GetCannibals(s)) =< Cardinality(GetMissionaries(s))

moveLeftToRightBank(S) ==
    /\ bank = "L"
    /\ S \subseteq leftBank
    /\  Cardinality(S) \in {1,2}
    /\ boat' = S
    /\ leftBank' = leftBank \ S
    /\ rightBank' = rightBank \union S
    /\ Guard(leftBank')
    /\ Guard(rightBank')
    /\ bank' = OtherBank("L")

moveRightToLeftBank(S) ==
    /\ bank = "R"
    /\ S \subseteq rightBank
    /\  Cardinality(S) \in {1,2}
    /\ boat' = S
    /\ rightBank' = rightBank \ S
    /\ leftBank' = leftBank \union S
    /\ Guard(leftBank')
    /\ Guard(rightBank')
    /\ bank' = OtherBank("R")

Next == \E s \in SUBSET Entities:
          /\ moveLeftToRightBank(s) \/ moveRightToLeftBank(s)
          \*/\ Cardinality(rightBank) /= 6 \* uncomment to see the solution of this problem

Spec == Init /\ [] [ Next ]_<<leftBank, rightBank, bank>>
====