Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
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

Lemma example_proof :
  problem_120_pre [-3; -4; 5] 3 /\
  problem_120_spec [-3; -4; 5] 3 [-4; -3; 5].
Proof.
  split.
  - unfold problem_120_pre.
    repeat split.
    + simpl. auto with arith.
    + simpl. auto with arith.
    + repeat constructor; unfold Z.le; simpl; auto with zarith.
    + simpl. auto with arith.
  - unfold problem_120_spec.
    repeat split.
    + reflexivity.
    + repeat constructor; unfold Z.le; simpl; auto with zarith.
    + exists [].
      split.
      * compute.
        apply Permutation_refl.
      * intros x y H1 H2.
        inversion H2.
Qed.