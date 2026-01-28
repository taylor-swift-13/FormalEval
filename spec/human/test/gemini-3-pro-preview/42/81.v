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
  [3.5652526206208957; 3.7; 8.9; 8.9] 
  [4.5652526206208957; 4.7; 9.9; 9.9].
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 4 (destruct i; [simpl; lra | ]).
    simpl in H. lia.
Qed.