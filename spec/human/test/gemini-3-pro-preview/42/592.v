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

(* Test case *)
Example problem_42_example : problem_42_spec 
  [-3.4; 10.746488790862529; 0; 3.2; -0.5; 5.9; 7.780292177637895; 5.9; 5.9; 3.2]
  [-2.4; 11.746488790862529; 1; 4.2; 0.5; 6.9; 8.780292177637895; 6.9; 6.9; 4.2].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 10 (destruct i; [simpl; lra | ]).
    simpl in H.
    lia.
Qed.