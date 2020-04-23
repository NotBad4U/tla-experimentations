# TLA<sup>+</sup> experimentations

List of experimentations made with the formal specification language TLA<sup>+</sup>.

## Missionaries and Cannibals problem

In the [missionaries and cannibals problem](https://en.wikipedia.org/wiki/Missionaries_and_cannibals_problem), three missionaries and three cannibals must cross a river using a boat which can carry at most two people, under the constraint that, for both banks, if there are missionaries present on the bank, they cannot be outnumbered by cannibals (if they were, the cannibals would eat the missionaries). The boat cannot cross the river by itself with no people on board. And, in some variations, one of the cannibals has only one arm and cannot row.

## Token Ring

Five silent philosophers sit at a round table with bowls of food. Forks are placed between each pair of adjacent philosophers.
The problem was designed to illustrate the challenges of avoiding deadlock, a system state in which no progress is possible.

## Dining Philosophers

There are 5 philosophers sitting around a table. Between each philosopher is a fork and, in order to eat a philosopher must hold both of the forks. (The spaghetti is really messy.) The philosophers cycle between 3 states: thinking, hungry, and eating. The dining philosopher protocol should satisfy 1. (safety) if a process is eating neither of its left neighbor or right neighbor can be eating, and 2. (progress) if a process is hungry, eventually it gets to eat.

*Formulation of the problem by Dijkstra*