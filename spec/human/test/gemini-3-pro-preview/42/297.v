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

(* Test case: input = [1.5; 8.6; 3.8; -2.1; 6.4; 1.5; 7.9; -2.1], output = [2.5; 9.6; 4.8; -1.1; 7.4; 2.5; 8.9; -1.1] *)
Example problem_42_example : problem_42_spec 
  [1.5%R; 8.6%R; 3.8%R; -2.1%R; 6.4%R; 1.5%R; 7.9%R; -2.1%R] 
  [2.5%R; 9.6%R; 4.8%R; -1.1%R; 7.4%R; 2.5%R; 8.9%R; -1.1%R].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 8 (destruct i as [|i]; [simpl; lra | simpl in H]).
    (* Since length is 8, i < 0 is a contradiction in nat *)
    lia.
Qed.