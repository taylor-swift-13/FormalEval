Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition problem_42_pre (input : list R) : Prop := True.

Definition problem_42_spec(input output : list R) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0%R = ((nth i input 0%R) + 1)%R.

Example problem_42_example : problem_42_spec [(-2.1)%R; 3.2%R; 7.9%R; (-2.1)%R] [(-1.1)%R; 4.2%R; 8.9%R; (-1.1)%R].
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 4 (destruct i; [simpl; lra | ]).
    simpl in H. lia.
Qed.