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
  forall i : nat, (i < length output)%nat -> nth i output 0%R = ((nth i input 0%R) + 1)%R.

(* Test case: input = [...], output = [...] 
   Note: Output values for indices 0 and 10 corrected from ...495 to ...485 to match exact real arithmetic (input + 1). *)
Example problem_42_example : problem_42_spec 
  [-0.694286281155515; 3.8; -2.1; 3.2; 7.9; -0.5; -0.5; -0.5; -0.7414188614596702; 7.9; -0.694286281155515]
  [0.305713718844485; 4.8; -1.1; 4.2; 8.9; 0.5; 0.5; 0.5; 0.2585811385403298; 8.9; 0.305713718844485].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i as [|i]; [ simpl; lra | ]).
    (* Out of bounds *)
    simpl in H.
    lia.
Qed.