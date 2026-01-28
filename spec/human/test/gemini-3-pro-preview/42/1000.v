Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition problem_42_pre (input : list R) : Prop := True.

Definition problem_42_spec(input output : list R) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0 = nth i input 0 + 1.

Example problem_42_example : problem_42_spec 
  [-3.4; -2; -0.5; 1; 3.2; 5.9; 7.9; 7.9] 
  [-2.4; -1; 0.5; 2; 4.2; 6.9; 8.9; 8.9].
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 8 (destruct i; [simpl; lra | ]).
    simpl in H. lia.
Qed.