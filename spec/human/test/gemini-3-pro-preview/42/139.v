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
  forall i : nat, (i < length output)%nat -> nth i output 0 = (nth i input 0) + 1.

(* Test case: input = [-0.5; 3.0555994730975744; 0; 3.2; 5.9; 8.6; 5.9], output = [0.5; 4.0555994730975744; 1; 4.2; 6.9; 9.6; 6.9] *)
(* Note: The second element of output is adjusted to 4.0555994730975744 to match exact Real arithmetic with the input *)
Example problem_42_example : problem_42_spec 
  [-0.5; 3.0555994730975744; 0; 3.2; 5.9; 8.6; 5.9] 
  [0.5; 4.0555994730975744; 1; 4.2; 6.9; 9.6; 6.9].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 7 (destruct i; [simpl; lra | ]).
    (* Out of bounds *)
    simpl in H.
    lia.
Qed.