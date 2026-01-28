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
  [-3.4; -0.5; 0; 3.2; -0.5; 5.9; 8.6; 5.9; 5.9] 
  [-2.4; 0.5; 1; 4.2; 0.5; 6.9; 9.6; 6.9; 6.9].
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 9 (destruct i; [simpl; lra | ]).
    simpl in H. lia.
Qed.