Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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

(* Test case: input = [1.5; ...], output = [2.5; ...] *)
Example problem_42_example : problem_42_spec 
  [1.5%R; 0.5071788072948802%R; 3.8%R; -2.707945416165158%R; 7.9%R; -2.8003143062363973%R] 
  [2.5%R; 1.5071788072948802%R; 4.8%R; -1.707945416165158%R; 8.9%R; -1.8003143062363973%R].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i as [|i]; [simpl; lra | ]).
    simpl in H.
    lia.
Qed.