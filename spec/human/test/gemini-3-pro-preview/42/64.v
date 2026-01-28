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

(* Test case: input = [-0.6821906440453559; 0.3; ...], output = [0.3178093559546441; 1.3; ...] *)
Example problem_42_example : problem_42_spec 
  [-0.6821906440453559%R; 0.3%R; -0.6821906440453559%R; -0.6821906440453559%R] 
  [0.3178093559546441%R; 1.3%R; 0.3178093559546441%R; 0.3178093559546441%R].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 4 (destruct i; [simpl; lra | ]).
    (* Out of bounds *)
    simpl in H.
    lia.
Qed.