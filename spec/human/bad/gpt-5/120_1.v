Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Definition problem_120_pre (arr : list Z) (k : nat) : Prop :=
       (length arr >= 1)%nat /\ (length arr <= 1000)%nat /\
       Forall (fun z => (-1000 <= z /\ z <= 1000)) arr /\
       (k <= length arr)%nat.

Definition problem_120_spec (arr : list Z) (k : nat) (res : list Z) : Prop :=
  length res = k /\
  Sorted Z.le res /\
  (exists rest_of_arr,
    Permutation (res ++ rest_of_arr) arr /\
    (forall x y, In x res -> In y rest_of_arr -> y <= x)).

Example problem_120_test_case_pre :
  problem_120_pre [-3%Z; -4%Z; 5%Z] 3%nat.
Proof.
  unfold problem_120_pre; simpl.
  repeat split.
  lia.
  lia.
  constructor.
  split; lia.
  constructor.
  split; lia.
  constructor.
  split; lia.
  constructor.
  lia.
Qed.

Example problem_120_test_case_spec :
  problem_120_spec [-3%Z; -4%Z; 5%Z] 3%nat [-4%Z; -3%Z; 5%Z].
Proof.
  unfold problem_120_spec; simpl.
  split.
  reflexivity.
  split.
  constructor.
  constructor.
  lia.
  constructor.
  lia.
  constructor.
  constructor.
  lia.
  constructor.
  constructor.
  constructor.
  exists ([] : list Z).
  split.
  simpl.
  apply perm_swap.
  intros x y Hx Hy.
  simpl in Hy.
  contradiction.
Qed.