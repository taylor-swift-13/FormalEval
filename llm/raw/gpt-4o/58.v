
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Structures.Equalities.

Definition common_spec (l1 l2 common : list nat) : Prop :=
  NoDup common /\
  (forall x, In x common <-> In x l1 /\ In x l2) /\
  Sorted Nat.le common.
