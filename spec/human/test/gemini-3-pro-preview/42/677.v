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

(* Test case: input = [2; 11; 4; 6; 8; 10; 12; 14; -5; 16; 8; 8; 4; 11], output = [3; 12; 5; 7; 9; 11; 13; 15; -4; 17; 9; 9; 5; 12] *)
Example problem_42_example : problem_42_spec [2%Z; 11%Z; 4%Z; 6%Z; 8%Z; 10%Z; 12%Z; 14%Z; -5%Z; 16%Z; 8%Z; 8%Z; 4%Z; 11%Z] [3%Z; 12%Z; 5%Z; 7%Z; 9%Z; 11%Z; 13%Z; 15%Z; -4%Z; 17%Z; 9%Z; 9%Z; 5%Z; 12%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i; [ simpl; reflexivity | ]).
    simpl in H.
    lia.
Qed.