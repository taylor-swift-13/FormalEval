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

Example test_case : strange_sort_list_spec [10; 9; 8; 10; 150; 6; 5; 10] [5; 150; 6; 10; 8; 10; 9; 10].
Proof.
  unfold strange_sort_list_spec.
  exists [5; 6; 8; 9; 10; 10; 10; 150].
  split.
  - (* Permutation *)
    (* 10 *)
    assert (H1: [5; 6; 8; 9; 10; 10; 10; 150] = [5; 6; 8; 9] ++ 10 :: [10; 10; 150]) by reflexivity.
    rewrite H1; clear H1. apply Permutation_cons_app. simpl.
    (* 9 *)
    assert (H2: [5; 6; 8; 9; 10; 10; 150] = [5; 6; 8] ++ 9 :: [10; 10; 150]) by reflexivity.
    rewrite H2; clear H2. apply Permutation_cons_app. simpl.
    (* 8 *)
    assert (H3: [5; 6; 8; 10; 10; 150] = [5; 6] ++ 8 :: [10; 10; 150]) by reflexivity.
    rewrite H3; clear H3. apply Permutation_cons_app. simpl.
    (* 10 *)
    assert (H4: [5; 6; 10; 10; 150] = [5; 6] ++ 10 :: [10; 150]) by reflexivity.
    rewrite H4; clear H4. apply Permutation_cons_app. simpl.
    (* 150 *)
    assert (H5: [5; 6; 10; 150] = [5; 6; 10] ++ 150 :: []) by reflexivity.
    rewrite H5; clear H5. apply Permutation_cons_app. simpl.
    (* 6 *)
    assert (H6: [5; 6; 10] = [5] ++ 6 :: [10]) by reflexivity.
    rewrite H6; clear H6. apply Permutation_cons_app. simpl.
    (* 5 *)
    assert (H7: [5; 10] = [] ++ 5 :: [10]) by reflexivity.
    rewrite H7; clear H7. apply Permutation_cons_app. simpl.
    (* 10 *)
    apply Permutation_refl.

  - split.
    + (* Sorted *)
      repeat constructor; try lia.
    + (* strange_interleave *)
      change [5; 6; 8; 9; 10; 10; 10; 150] with (5 :: [6; 8; 9; 10; 10; 10] ++ [150]).
      apply si_step.
      change [6; 8; 9; 10; 10; 10] with (6 :: [8; 9; 10; 10] ++ [10]).
      apply si_step.
      change [8; 9; 10; 10] with (8 :: [9; 10] ++ [10]).
      apply si_step.
      change [9; 10] with (9 :: [] ++ [10]).
      apply si_step.
      apply si_nil.
Qed.