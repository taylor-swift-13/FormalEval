Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition problem_42_pre (input : list R) : Prop := True.

Definition problem_42_spec(input output : list R) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0 = (nth i input 0) + 1.

Example problem_42_example : problem_42_spec 
  [2.443642398169077; -3.4; -2; -0.5; 0; 5.9; 8.6; 3.8] 
  [3.443642398169077; -2.4; -1; 0.5; 1; 6.9; 9.6; 4.8].
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 8 (destruct i; [simpl; lra | simpl in H]).
    lia.
Qed.