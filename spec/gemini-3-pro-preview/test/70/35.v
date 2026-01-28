Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Inductive strange_interleave : list Z -> list Z -> Prop :=
| si_nil : strange_interleave [] []
| si_one : forall x, strange_interleave [x] [x]
| si_step : forall x y mid res,
    strange_interleave mid res ->
    strange_interleave (x :: mid ++ [y]) (x :: y :: res).

Definition strange_sort_list_spec (lst : list Z) (ans : list Z) : Prop :=
  exists sorted_lst,
    Permutation lst sorted_lst /\
    Sorted Z.le sorted_lst /\
    strange_interleave sorted_lst ans.

Example test_case : strange_sort_list_spec [2; 4; 6; 8; 1; 10; 12] [1; 12; 2; 10; 4; 8; 6].
Proof.
  unfold strange_sort_list_spec.
  exists [1; 2; 4; 6; 8; 10; 12].
  split.
  - apply Permutation_sym.
    change [2; 4; 6; 8; 1; 10; 12] with ([2; 4; 6; 8] ++ 1 :: [10; 12]).
    change [1; 2; 4; 6; 8; 10; 12] with (1 :: [2; 4; 6; 8] ++ [10; 12]).
    apply Permutation_middle.
  - split.
    + repeat constructor; try lia.
    + change [1; 2; 4; 6; 8; 10; 12] with (1 :: [2; 4; 6; 8; 10] ++ [12]).
      apply si_step.
      change [2; 4; 6; 8; 10] with (2 :: [4; 6; 8] ++ [10]).
      apply si_step.
      change [4; 6; 8] with (4 :: [6] ++ [8]).
      apply si_step.
      apply si_one.
Qed.