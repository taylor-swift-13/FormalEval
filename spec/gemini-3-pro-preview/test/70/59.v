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

Example test_case : strange_sort_list_spec [200; 300; 200; 35; 100] [35; 300; 100; 200; 200].
Proof.
  unfold strange_sort_list_spec.
  exists [35; 100; 200; 200; 300].
  split.
  - apply Permutation_sym.
    change [200; 300; 200; 35; 100] with ([200; 300; 200] ++ 35 :: [100]).
    apply Permutation_cons_app. simpl.
    change [200; 300; 200; 100] with ([200; 300; 200] ++ 100 :: []).
    apply Permutation_cons_app. simpl.
    change [200; 300; 200] with ([] ++ 200 :: [300; 200]).
    apply Permutation_cons_app. simpl.
    change [300; 200] with ([300] ++ 200 :: []).
    apply Permutation_cons_app. simpl.
    apply Permutation_refl.
  - split.
    + repeat constructor; try lia.
    + change [35; 100; 200; 200; 300] with (35 :: [100; 200; 200] ++ [300]).
      apply si_step.
      change [100; 200; 200] with (100 :: [200] ++ [200]).
      apply si_step.
      apply si_one.
Qed.