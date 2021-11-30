# Separation logic demos

[![CI](https://github.com/tchajed/seplogic-demo/actions/workflows/build.yml/badge.svg)](https://github.com/tchajed/seplogic-demo/actions/workflows/build.yml)

Some simple examples of (sequential) separation logic, using Iris to give
complete proofs. These examples are taken from "[Separation
Logic](https://cacm.acm.org/magazines/2019/2/234356-separation-logic/fulltext)"
by Peter O'Hearn, from CACM 2019.

The two main examples are:

- [delete_tree.v](src/delete_tree.v), which proves that freeing a tree
  recursively is safe, and
- [binary_search.v](src/binary_search.v), which proves functional correctness of
  the insert and search procedures for a binary search tree.
