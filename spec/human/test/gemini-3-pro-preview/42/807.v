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

(* Test case: input = [3.8%R; -2.1%R; 9.406367499891232%R; 3.2%R; 7.9%R; -2.1%R], output = [4.8%R; -1.1%R; 10.406367499891232%R; 4.2%R; 8.9%R; -1.1%R] *)
Example problem_42_example : problem_42_spec 
  [3.8%R; -2.1%R; 9.406367499891232%R; 3.2%R; 7.9%R; -2.1%R] 
  [4.8%R; -1.1%R; 10.406367499891232%R; 4.2%R; 8.9%R; -1.1%R].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 6 (destruct i as [|i]; [simpl; lra | ]).
    (* Out of bounds *)
    simpl in H.
    lia.
Qed.