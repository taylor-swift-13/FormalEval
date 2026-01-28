Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `incr_list` *)
Definition problem_42_pre (input : list R) : Prop := True.

(* Note: explicitly use %nat for the length comparison *)
Definition problem_42_spec(input output : list R) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0 = (nth i input 0) + 1.

(* Test case: input = [-0.5; ...], output = [0.5; ...] *)
Example problem_42_example : problem_42_spec 
  [-0.5; 3.0555994730975744; 0; 5.9; 8.6; 5.9; 7.041313375938212; 5.9; 1.5; 5.9; 8.6] 
  [0.5; 4.0555994730975744; 1; 6.9; 9.6; 6.9; 8.041313375938212; 6.9; 2.5; 6.9; 9.6].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    simpl in H.
    (* Verify element-wise equality for all indices *)
    repeat (destruct i as [|i]; [ simpl; lra | ]).
    (* The remaining case contradicts the length bound *)
    simpl in H.
    lia.
Qed.