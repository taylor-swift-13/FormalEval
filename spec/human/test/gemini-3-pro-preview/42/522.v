Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `incr_list` *)
Definition problem_42_pre (input : list R) : Prop := True.

(* Note: explicitly use %nat for the length comparison to avoid conflict with R_scope *)
Definition problem_42_spec(input output : list R) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0 = ((nth i input 0) + 1).

(* Test case: input = [-0.5; 1.5; 3.8; 6.4; 7.9; 6.4], output = [0.5; 2.5; 4.8; 7.4; 8.9; 7.4] *)
Example problem_42_example : problem_42_spec [-0.5%R; 1.5%R; 3.8%R; 6.4%R; 7.9%R; 6.4%R] [0.5%R; 2.5%R; 4.8%R; 7.4%R; 8.9%R; 7.4%R].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 6 (destruct i; [simpl; lra | simpl in H]).
    lia.
Qed.