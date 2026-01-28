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

Example test_case : strange_sort_list_spec [10; 9; 8; 10; 150; 6; 5] [5; 150; 6; 10; 8; 10; 9].
Proof.
  unfold strange_sort_list_spec.
  exists [5; 6; 8; 9; 10; 10; 150].
  split.
  - change [10; 9; 8; 10; 150; 6; 5] with ([10; 9; 8; 10; 150; 6] ++ [5]).
    apply Permutation_trans with (5 :: [10; 9; 8; 10; 150; 6]).
    { apply Permutation_sym. apply Permutation_cons_append. }
    apply perm_skip.
    change [10; 9; 8; 10; 150; 6] with ([10; 9; 8; 10; 150] ++ [6]).
    apply Permutation_trans with (6 :: [10; 9; 8; 10; 150]).
    { apply Permutation_sym. apply Permutation_cons_append. }
    apply perm_skip.
    change [10; 9; 8; 10; 150] with ([10; 9] ++ 8 :: [10; 150]).
    apply Permutation_trans with (8 :: [10; 9] ++ [10; 150]).
    { apply Permutation_sym. apply Permutation_middle. }
    apply perm_skip.
    change ([10; 9] ++ [10; 150]) with ([10] ++ 9 :: [10; 150]).
    apply Permutation_trans with (9 :: [10] ++ [10; 150]).
    { apply Permutation_sym. apply Permutation_middle. }
    apply perm_skip.
    apply Permutation_refl.
  - split.
    + repeat constructor; try lia.
    + change [5; 6; 8; 9; 10; 10; 150] with (5 :: [6; 8; 9; 10; 10] ++ [150]).
      apply si_step.
      change [6; 8; 9; 10; 10] with (6 :: [8; 9; 10] ++ [10]).
      apply si_step.
      change [8; 9; 10] with (8 :: [9] ++ [10]).
      apply si_step.
      apply si_one.
Qed.