
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.

Open Scope Z_scope.
Open Scope nat_scope.

Parameter ones_in_bin : Z -> nat.

Definition cmp_rel (x y : Z) : Prop :=
  ones_in_bin x < ones_in_bin y \/ (ones_in_bin x = ones_in_bin y /\ x <= y).

Definition sort_array_spec (arr : list Z) (res : list Z) : Prop :=
  Permutation res arr /\ Sorted cmp_rel res.
