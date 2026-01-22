# Tower of Hanoi

A formalization of the [Tower of Hanoi](https://en.wikipedia.org/wiki/Tower_of_Hanoi) game and its generalizations.

## Objectives

- [ ] **1** - Construct the walk that solves the classic configuration of `n` blocks on `3` towers and prove that its length is `2 ^ n - 1`.
- [ ] **2** - Prove that any solution of length less than `2 ^ n` to the classic configuration of `n` blocks on `3` towers is equal to the previous solution.

## Roadmap

### Objective 1

- [X] Configurations, moves, and walks in Tower of Hanoi with towers from some type and blocks from some totally-ordered type. A block can only be moved to and from towers containing only greater blocks.
- [X] Map configurations, moves, and walks between isomorphic types.
- [X] Map moves and walks in a lower subset of all the blocks to moves and walks in all the blocks.
- [X] Append and reverse walks.
