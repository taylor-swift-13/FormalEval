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

Lemma collatz_3 : collatz_list 3 [3; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_odd with (l' := [10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_10.
Qed.

Lemma collatz_6 : collatz_list 6 [6; 3; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [3; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_3.
Qed.

Lemma collatz_12 : collatz_list 12 [12; 6; 3; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [6; 3; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_6.
Qed.

Lemma sorted_result : Sorted Z.le [1; 3; 5].
Proof.
  repeat constructor; lia.
Qed.

Lemma perm_helper : Permutation [1; 3; 5] [3; 5; 1].
Proof.
  apply Permutation_sym.
  assert (H1: Permutation [3; 5; 1] [1; 3; 5]).
  {
    change [3; 5; 1] with ([3; 5] ++ [1]).
    change [1; 3; 5] with ([1] ++ [3; 5]).
    apply Permutation_app_comm.
  }
  apply H1.
Qed.

Example problem_123_test :
  problem_123_spec 12 [1; 3; 5].
Proof.
  unfold problem_123_spec.
  exists [12; 6; 3; 10; 5; 16; 8; 4; 2; 1].
  split.
  - apply collatz_12.
  - split.
    + simpl.
      apply perm_helper.
    + apply sorted_result.
Qed.