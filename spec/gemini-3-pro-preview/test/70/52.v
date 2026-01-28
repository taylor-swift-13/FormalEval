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

Example test_case : strange_sort_list_spec [200; 300; 150; 35; 100; 35] [35; 300; 35; 200; 100; 150].
Proof.
  unfold strange_sort_list_spec.
  exists [35; 35; 100; 150; 200; 300].
  split.
  - replace [35; 35; 100; 150; 200; 300] with ([35; 35; 100; 150] ++ 200 :: [300]) by reflexivity.
    apply Permutation_cons_app. simpl.
    replace [35; 35; 100; 150; 300] with ([35; 35; 100; 150] ++ 300 :: []) by reflexivity.
    apply Permutation_cons_app. simpl.
    replace [35; 35; 100; 150] with ([35; 35; 100] ++ 150 :: []) by reflexivity.
    apply Permutation_cons_app. simpl.
    replace [35; 35; 100] with ([] ++ 35 :: [35; 100]) by reflexivity.
    apply Permutation_cons_app. simpl.
    replace [35; 100] with ([35] ++ 100 :: []) by reflexivity.
    apply Permutation_cons_app. simpl.
    apply Permutation_refl.
  - split.
    + repeat constructor; try lia.
    + change [35; 35; 100; 150; 200; 300] with (35 :: [35; 100; 150; 200] ++ [300]).
      apply si_step.
      change [35; 100; 150; 200] with (35 :: [100; 150] ++ [200]).
      apply si_step.
      change [100; 150] with (100 :: [] ++ [150]).
      apply si_step.
      apply si_nil.
Qed.