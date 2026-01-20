Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.

Open Scope Z_scope.

Definition maximum_spec (arr : list Z) (k : nat) (res : list Z) : Prop :=
  k <= length arr /\
  exists s : list Z,
    Permutation s arr /\
    Sorted (fun x y => Z.ge x y) s /\
    Permutation res (firstn k s) /\
    Sorted (fun x y => Z.le x y) res.