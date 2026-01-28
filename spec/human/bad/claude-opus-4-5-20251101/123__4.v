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

Lemma sorted_result_1 : Sorted Z.le [1].
Proof.
  constructor.
Qed.

Lemma perm_helper_1 : Permutation [1] [1].
Proof.
  apply Permutation_refl.
Qed.

Example problem_123_test :
  problem_123_spec 1 [1].
Proof.
  unfold problem_123_spec.
  exists [1].
  split.
  - apply collatz_1.
  - split.
    + simpl.
      apply perm_helper_1.
    + apply sorted_result_1.
Qed.