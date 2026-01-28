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

(* Test case: input = [1; 4; 6; 8; -4; 20; 16; 15; 20; 16; 4; 15; 20], output = [2; 5; 7; 9; -3; 21; 17; 16; 21; 17; 5; 16; 21] *)
Example problem_42_example : problem_42_spec 
  [1%Z; 4%Z; 6%Z; 8%Z; -4%Z; 20%Z; 16%Z; 15%Z; 20%Z; 16%Z; 4%Z; 15%Z; 20%Z] 
  [2%Z; 5%Z; 7%Z; 9%Z; -3%Z; 21%Z; 17%Z; 16%Z; 21%Z; 17%Z; 5%Z; 16%Z; 21%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i as [|i]; [simpl; reflexivity | simpl in H]).
    lia.
Qed.