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

(* Test case: input = [0.1; 0.2], output = [1.1; 1.2] *)
Example problem_42_example : problem_42_spec [0.1%R; 0.2%R] [1.1%R; 1.2%R].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    simpl in H.
    destruct i.
    + (* i = 0 *)
      simpl.
      lra.
    + destruct i.
      * (* i = 1 *)
        simpl.
        lra.
      * (* i >= 2 *)
        simpl in H.
        lia.
Qed.