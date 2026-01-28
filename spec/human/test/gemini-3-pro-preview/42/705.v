Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `incr_list` *)
Definition problem_42_pre (input : list R) : Prop := True.

(* Note: explicitly use %nat for the length comparison to avoid conflict with R_scope *)
Definition problem_42_spec(input output : list R) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0%R = ((nth i input 0%R) + 1)%R.

(* Test case: input = [-0.5; 3.8; -2.1; 3.2; 7.9; -0.5], output = [0.5; 4.8; -1.1; 4.2; 8.9; 0.5] *)
Example problem_42_example : problem_42_spec 
  [-0.5; 3.8; -2.1; 3.2; 7.9; -0.5]%R 
  [0.5; 4.8; -1.1; 4.2; 8.9; 0.5]%R.
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 6 (destruct i; [simpl; lra | ]).
    simpl in H.
    lia.
Qed.