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

(* Test case: input = [2.5; 3.7; 1.1; 0.5], output = [3.5; 4.7; 2.1; 1.5] *)
Example problem_42_example : problem_42_spec [2.5%R; 3.7%R; 1.1%R; 0.5%R] [3.5%R; 4.7%R; 2.1%R; 1.5%R].
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