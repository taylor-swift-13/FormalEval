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

Lemma collatz_13 : collatz_list 13 [13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_odd with (l' := [40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_40.
Qed.

Lemma collatz_26 : collatz_list 26 [26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_13.
Qed.

Lemma collatz_52 : collatz_list 52 [52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_26.
Qed.

Lemma collatz_17 : collatz_list 17 [17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_odd with (l' := [52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_52.
Qed.

Lemma collatz_34 : collatz_list 34 [34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_17.
Qed.

Lemma collatz_11 : collatz_list 11 [11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_odd with (l' := [34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_34.
Qed.

Lemma collatz_22 : collatz_list 22 [22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_11.
Qed.

Lemma collatz_44 : collatz_list 44 [44; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_22.
Qed.

Lemma collatz_88 : collatz_list 88 [88; 44; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_even with (l' := [44; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_44.
Qed.

Lemma collatz_29 : collatz_list 29 [29; 88; 44; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
Proof.
  apply cl_odd with (l' := [88; 44; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1]).
  - lia.
  - reflexivity.
  - apply collatz_88.
Qed.

Lemma sorted_result_29 : Sorted Z.le [1; 5; 11; 13; 17; 29].
Proof.
  repeat constructor; lia.
Qed.

Lemma perm_helper_29 : Permutation [1; 5; 11; 13; 17; 29] [29; 11; 17; 13; 5; 1].
Proof.
  apply Permutation_sym.
  assert (H1: Permutation [29; 11; 17; 13; 5; 1] [1; 29; 11; 17; 13; 5]).
  {
    change [29; 11; 17; 13; 5; 1] with ([29; 11; 17; 13; 5] ++ [1]).
    change [1; 29; 11; 17; 13; 5] with ([1] ++ [29; 11; 17; 13; 5]).
    apply Permutation_app_comm.
  }
  eapply Permutation_trans. apply H1.
  assert (H2: Permutation [1; 29; 11; 17; 13; 5] [1; 5; 29; 11; 17; 13]).
  {
    apply perm_skip.
    change [29; 11; 17; 13; 5] with ([29; 11; 17; 13] ++ [5]).
    change [5; 29; 11; 17; 13] with ([5] ++ [29; 11; 17; 13]).
    apply Permutation_app_comm.
  }
  eapply Permutation_trans. apply H2.
  assert (H3: Permutation [1; 5; 29; 11; 17; 13] [1; 5; 11; 29; 17; 13]).
  {
    apply perm_skip. apply perm_skip. apply perm_swap.
  }
  eapply Permutation_trans. apply H3.
  assert (H4: Permutation [1; 5; 11; 29; 17; 13] [1; 5; 11; 13; 29; 17]).
  {
    apply perm_skip. apply perm_skip. apply perm_skip.
    change [29; 17; 13] with ([29; 17] ++ [13]).
    change [13; 29; 17] with ([13] ++ [29; 17]).
    apply Permutation_app_comm.
  }
  eapply Permutation_trans. apply H4.
  assert (H5: Permutation [1; 5; 11; 13; 29; 17] [1; 5; 11; 13; 17; 29]).
  {
    apply perm_skip. apply perm_skip. apply perm_skip. apply perm_skip.
    apply perm_swap.
  }
  apply H5.
Qed.

Example problem_123_test :
  problem_123_spec 29 [1; 5; 11; 13; 17; 29].
Proof.
  unfold problem_123_spec.
  exists [29; 88; 44; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
  split.
  - apply collatz_29.
  - split.
    + simpl.
      apply perm_helper_29.
    + apply sorted_result_29.
Qed.