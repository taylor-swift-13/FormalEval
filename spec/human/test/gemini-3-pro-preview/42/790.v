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
  forall i : nat, (i < length output)%nat -> nth i output 0 = ((nth i input 0) + 1).

(* Test case: input = [1.5; 3.8; -2.1; 7.9; 3.8], output = [2.5; 4.8; -1.1; 8.9; 4.8] *)
Example problem_42_example : problem_42_spec 
  [1.5%R; 3.8%R; -2.1%R; 7.9%R; 3.8%R] 
  [2.5%R; 4.8%R; -1.1%R; 8.9%R; 4.8%R].
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