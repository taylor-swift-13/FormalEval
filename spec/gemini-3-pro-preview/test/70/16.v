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

Example test_case : strange_sort_list_spec [2; 1; 4; 3; 6; 5] [1; 6; 2; 5; 3; 4].
Proof.
  unfold strange_sort_list_spec.
  exists [1; 2; 3; 4; 5; 6].
  split.
  - apply perm_trans with (l' := [1; 2; 4; 3; 6; 5]).
    + apply perm_swap.
    + apply perm_skip. apply perm_skip.
      apply perm_trans with (l' := [3; 4; 6; 5]).
      * apply perm_swap.
      * apply perm_skip. apply perm_skip.
        apply perm_swap.
  - split.
    + repeat constructor; try lia.
    + change [1; 2; 3; 4; 5; 6] with (1 :: [2; 3; 4; 5] ++ [6]).
      apply si_step.
      change [2; 3; 4; 5] with (2 :: [3; 4] ++ [5]).
      apply si_step.
      change [3; 4] with (3 :: [] ++ [4]).
      apply si_step.
      apply si_nil.
Qed.