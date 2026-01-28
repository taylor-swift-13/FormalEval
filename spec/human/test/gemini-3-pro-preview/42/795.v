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
  forall i : nat, (i < length output)%nat -> nth i output 0%R = ((nth i input 0%R) + 1)%R.

(* Test case: input = [-3.4; -2; 8.6; 1; 3.2; 5.9; 8.6], output = [-2.4; -1; 9.6; 2; 4.2; 6.9; 9.6] *)
Example problem_42_example : problem_42_spec 
  [-3.4; -2; 8.6; 1; 3.2; 5.9; 8.6] 
  [-2.4; -1; 9.6; 2; 4.2; 6.9; 9.6].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 7 (destruct i; [simpl; lra | ]).
    simpl in H.
    lia.
Qed.