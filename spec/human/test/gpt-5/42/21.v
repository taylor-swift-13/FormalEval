Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Lia.
Require Import Lra.
Import ListNotations.

Definition problem_42_pre (input : list R) : Prop := True.

Definition problem_42_spec(input output : list R) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%R = ((nth i input 0%R) + 1%R)%R.

Example problem_42_test_case : problem_42_spec [0.1%R; 0.3%R] [1.1%R; 1.3%R].
Proof.
  unfold problem_42_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi.
    destruct i as [| i'].
    + simpl. lra.
    + destruct i' as [| i''].
      * simpl. lra.
      * simpl in Hi. exfalso. lia.
Qed.