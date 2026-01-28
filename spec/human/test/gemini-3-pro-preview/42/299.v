Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Floats.Floats.
Import ListNotations.
Open Scope float_scope.

(* Pre: no special constraints for `incr_list` *)
Definition problem_42_pre (input : list float) : Prop := True.

(* Note: explicitly use %nat for the length comparison to avoid conflict with float_scope *)
Definition problem_42_spec(input output : list float) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0 = ((nth i input 0) + 1).

(* Test case: input = [-0.5; ...], output = [0.5; ...] *)
Example problem_42_example : problem_42_spec 
  [-0.5; 3.0555994730975744; 0; 3.8745762456886825; 5.9; 8.6; 5.9; 7.9; 5.9] 
  [0.5; 4.055599473097574; 1; 4.874576245688683; 6.9; 9.6; 6.9; 8.9; 6.9].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 9 (destruct i; [ vm_compute; reflexivity | ]).
    (* Handle out of bounds *)
    simpl in H.
    lia.
Qed.