Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Lia.

Import ListNotations.
Open Scope Z_scope.

Inductive collatz_list (n : Z) : list Z -> Prop :=
  | cl_one : n = 1 -> collatz_list n [1]
  | cl_even : forall l',
      n > 1 ->
      Z.even n = true ->
      collatz_list (n / 2) l' ->
      collatz_list n (n :: l')
  | cl_odd : forall l',
      n > 1 ->
      Z.odd n = true ->
      collatz_list (3 * n + 1) l' ->
      collatz_list n (n :: l').

Definition problem_123_pre (n : Z) : Prop := n > 0.

Definition problem_123_spec (n : Z) (result : list Z) : Prop :=
  exists (c_seq : list Z),
    collatz_list n c_seq /\
    Permutation result (filter (fun x => Z.odd x) c_seq) /\
    Sorted Z.le result.

Lemma collatz_1 : collatz_list 1 [1].
Proof. apply cl_one. reflexivity. Qed.

Lemma collatz_2 : collatz_list 2 [2; 1].
Proof.
  apply cl_even with (l' := [1]).
  - lia.
  - reflexivity.
  - apply collatz_1.
Qed.

Lemma collatz_4 : collatz_list 4 [4; 2; 1].
Proof.
  apply cl_even with (l' := [2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_2.
Qed.

Lemma collatz_8 : collatz_list 8 [8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_4.
Qed.

Lemma collatz_16 : collatz_list 16 [16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_8.
Qed.

Lemma collatz_5 : collatz_list 5 [5; 16; 8; 4; 2; 1].
Proof.
  apply cl_odd with (l' := [16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_16.
Qed.

Lemma collatz_10 : collatz_list 10 [10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_5.
Qed.

Lemma collatz_20 : collatz_list 20 [20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_10.
Qed.

Lemma collatz_40 : collatz_list 40 [40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_20.
Qed.

Lemma collatz_80 : collatz_list 80 [80; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_40.
Qed.

Lemma collatz_160 : collatz_list 160 [160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [80; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_80.
Qed.

Lemma collatz_53 : collatz_list 53 [53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_odd with (l' := [160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_160.
Qed.

Lemma collatz_106 : collatz_list 106 [106; 53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_53.
Qed.

Lemma collatz_35 : collatz_list 35 [35; 106; 53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_odd with (l' := [106; 53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_106.
Qed.

Lemma collatz_70 : collatz_list 70 [70; 35; 106; 53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [35; 106; 53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_35.
Qed.

Lemma collatz_23 : collatz_list 23 [23; 70; 35; 106; 53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_odd with (l' := [70; 35; 106; 53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_70.
Qed.

Lemma collatz_46 : collatz_list 46 [46; 23; 70; 35; 106; 53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [23; 70; 35; 106; 53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_23.
Qed.

Lemma collatz_15 : collatz_list 15 [15; 46; 23; 70; 35; 106; 53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_odd with (l' := [46; 23; 70; 35; 106; 53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_46.
Qed.

Lemma sorted_result_15 : Sorted Z.le [1; 5; 15; 23; 35; 53].
Proof.
  repeat constructor; lia.
Qed.

Lemma perm_helper_15 : Permutation [1; 5; 15; 23; 35; 53] [15; 23; 35; 53; 5; 1].
Proof.
  apply Permutation_sym.
  assert (H1: Permutation [15; 23; 35; 53; 5; 1] [1; 15; 23; 35; 53; 5]).
  {
    change [15; 23; 35; 53; 5; 1] with ([15; 23; 35; 53; 5] ++ [1]).
    change [1; 15; 23; 35; 53; 5] with ([1] ++ [15; 23; 35; 53; 5]).
    apply Permutation_app_comm.
  }
  eapply Permutation_trans. apply H1.
  assert (H2: Permutation [1; 15; 23; 35; 53; 5] [1; 5; 15; 23; 35; 53]).
  {
    apply perm_skip.
    change [15; 23; 35; 53; 5] with ([15; 23; 35; 53] ++ [5]).
    change [5; 15; 23; 35; 53] with ([5] ++ [15; 23; 35; 53]).
    apply Permutation_app_comm.
  }
  eapply Permutation_trans. apply H2.
  apply Permutation_refl.
Qed.

Example problem_123_test :
  problem_123_spec 15 [1; 5; 15; 23; 35; 53].
Proof.
  unfold problem_123_spec.
  exists [15; 46; 23; 70; 35; 106; 53; 160; 80; 40; 20; 10; 5; 16; 8; 4; 2; 1].
  split.
  - apply collatz_15.
  - split.
    + simpl.
      apply perm_helper_15.
    + apply sorted_result_15.
Qed.