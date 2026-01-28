Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope R_scope.

Definition problem_42_pre (input : list R) : Prop := True.

Definition problem_42_spec(input output : list R) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0 = (nth i input 0) + 1.

Example problem_42_example : problem_42_spec [-0.5; 3.8; -2.1; 6.4; 7.9] [0.5; 4.8; -1.1; 7.4; 8.9].
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [simpl; lra | ]).
    simpl in H. lia.
Qed.