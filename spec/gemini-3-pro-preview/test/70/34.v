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

Example test_case : strange_sort_list_spec [-5; 151; 4; 9; -5] [-5; 151; -5; 9; 4].
Proof.
  unfold strange_sort_list_spec.
  exists [-5; -5; 4; 9; 151].
  split.
  - apply perm_skip.
    replace [151; 4; 9; -5] with ([151; 4; 9] ++ [-5]) by reflexivity.
    apply Permutation_trans with (l' := [-5] ++ [151; 4; 9]).
    + apply Permutation_app_comm.
    + simpl. apply perm_skip.
      replace [151; 4; 9] with ([151] ++ [4; 9]) by reflexivity.
      apply Permutation_trans with (l' := [4; 9] ++ [151]).
      * apply Permutation_app_comm.
      * simpl. apply Permutation_refl.
  - split.
    + repeat constructor; try lia.
    + change [-5; -5; 4; 9; 151] with (-5 :: [-5; 4; 9] ++ [151]).
      apply si_step.
      change [-5; 4; 9] with (-5 :: [4] ++ [9]).
      apply si_step.
      apply si_one.
Qed.