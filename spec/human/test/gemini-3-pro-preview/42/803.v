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

(* Test case: input = [-3.4%R; -0.5%R; 3.8%R; 3.2%R; 7.9%R; -0.5%R], output = [-2.4%R; 0.5%R; 4.8%R; 4.2%R; 8.9%R; 0.5%R] *)
Example problem_42_example : problem_42_spec 
  [-3.4%R; -0.5%R; 3.8%R; 3.2%R; 7.9%R; -0.5%R] 
  [-2.4%R; 0.5%R; 4.8%R; 4.2%R; 8.9%R; 0.5%R].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i as [|i]; [simpl; lra | ]).
    (* Since length is 6, i >= 6 is a contradiction in nat *)
    simpl in H.
    lia.
Qed.