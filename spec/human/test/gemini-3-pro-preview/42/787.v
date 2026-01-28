Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope R_scope.

Definition problem_42_pre (input : list R) : Prop := True.

Definition problem_42_spec(input output : list R) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0%R = ((nth i input 0%R) + 1)%R.

Example problem_42_example : problem_42_spec 
  [8.6%R; -0.5%R; 3.8%R; -2.1%R; 3.2%R; 7.9%R; -0.5%R; 3.2%R; 8.6%R] 
  [9.6%R; 0.5%R; 4.8%R; -1.1%R; 4.2%R; 8.9%R; 0.5%R; 4.2%R; 9.6%R].
Proof.
  unfold problem_42_spec.
  split.
  - simpl.
    reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [simpl; lra | ]).
    simpl in H.
    lia.
Qed.