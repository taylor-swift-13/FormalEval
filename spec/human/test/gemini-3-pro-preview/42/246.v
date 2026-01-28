Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `incr_list` *)
Definition problem_42_pre (input : list Z) : Prop := True.

(* Note: explicitly use %nat for the length comparison to avoid conflict with Z_scope *)
Definition problem_42_spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

(* Test case: input = [1; 4; 6; 15; 8; 10; 20; 6; 20], output = [2; 5; 7; 16; 9; 11; 21; 7; 21] *)
Example problem_42_example : problem_42_spec [1; 4; 6; 15; 8; 10; 20; 6; 20] [2; 5; 7; 16; 9; 11; 21; 7; 21].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 9 (destruct i; [ simpl; reflexivity | simpl in H ]).
    (* Remaining case: i >= 9, which contradicts H (i < 9) *)
    lia.
Qed.