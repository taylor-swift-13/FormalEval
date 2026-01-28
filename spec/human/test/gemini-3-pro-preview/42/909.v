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

(* Test case: input = [-0.5; ...], output = [0.5; ...] *)
Example problem_42_example : problem_42_spec 
  [-0.5; 3.8; -2.1; 1.5; 3.2; 7.34483500474661; -0.7414188614596702; 3.8; 1.5]
  [0.5; 4.8; -1.1; 2.5; 4.2; 8.34483500474661; 0.2585811385403298; 4.8; 2.5].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 9 (destruct i; [ simpl; lra | ]).
    (* Out of bounds *)
    simpl in H.
    lia.
Qed.