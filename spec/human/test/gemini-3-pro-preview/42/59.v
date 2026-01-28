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
  forall i : nat, (i < length output)%nat -> nth i output 0 = (nth i input 0) + 1.

(* Test case: input = [3.5652526206208957; 3.7; 8.9; 1.2; 0.5], output = [4.5652526206208957; 4.7; 9.9; 2.2; 1.5] *)
Example problem_42_example : problem_42_spec 
  [3.5652526206208957%R; 3.7%R; 8.9%R; 1.2%R; 0.5%R] 
  [4.5652526206208957%R; 4.7%R; 9.9%R; 2.2%R; 1.5%R].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 5 (destruct i as [|i]; [simpl; lra | ]).
    simpl in H.
    lia.
Qed.