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

Example test_case : strange_sort_list_spec [10; 9; 8; 75; 6; 5] [5; 75; 6; 10; 8; 9].
Proof.
  unfold strange_sort_list_spec.
  exists [5; 6; 8; 9; 10; 75].
  split.
  - transitivity (5 :: [10; 9; 8; 75; 6]).
    + change [10; 9; 8; 75; 6; 5] with ([10; 9; 8; 75; 6] ++ 5 :: []).
      apply Permutation_sym, Permutation_middle.
    + apply perm_skip.
      transitivity (6 :: [10; 9; 8; 75]).
      * change [10; 9; 8; 75; 6] with ([10; 9; 8; 75] ++ 6 :: []).
        apply Permutation_sym, Permutation_middle.
      * apply perm_skip.
        transitivity (8 :: [10; 9; 75]).
        -- change [10; 9; 8; 75] with ([10; 9] ++ 8 :: [75]).
           apply Permutation_sym, Permutation_middle.
        -- apply perm_skip.
           transitivity (9 :: [10; 75]).
           ++ change [10; 9; 75] with ([10] ++ 9 :: [75]).
              apply Permutation_sym, Permutation_middle.
           ++ apply perm_skip.
              apply Permutation_refl.
  - split.
    + repeat constructor; try lia.
    + change [5; 6; 8; 9; 10; 75] with (5 :: [6; 8; 9; 10] ++ [75]).
      apply si_step.
      change [6; 8; 9; 10] with (6 :: [8; 9] ++ [10]).
      apply si_step.
      change [8; 9] with (8 :: [] ++ [9]).
      apply si_step.
      apply si_nil.
Qed.