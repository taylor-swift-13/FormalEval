
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Structures.Equalities.

Definition unique_spec (l : list nat) (result : list nat) : Prop :=
  NoDup result /\
  Permutation result (nodup Nat.eq_dec l) /\
  Sorted Nat.le result.
