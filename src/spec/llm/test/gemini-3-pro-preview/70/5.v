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

Example test_case : strange_sort_list_spec [5; 5; 5; 5] [5; 5; 5; 5].
Proof.
  unfold strange_sort_list_spec.
  exists [5; 5; 5; 5].
  split.
  - apply Permutation_refl.
  - split.
    + repeat constructor; try lia.
    + change [5; 5; 5; 5] with (5 :: [5; 5] ++ [5]).
      apply si_step.
      change [5; 5] with (5 :: [] ++ [5]).
      apply si_step.
      apply si_nil.
Qed.