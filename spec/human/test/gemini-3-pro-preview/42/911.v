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

(* Test case: input = [1; -2; -3; 3; -4; -1; -1; -6; 7; -8; 9; -10; -4; 3; -4], output = [2; -1; -2; 4; -3; 0; 0; -5; 8; -7; 10; -9; -3; 4; -3] *)
Example problem_42_example : problem_42_spec [1%Z; -2%Z; -3%Z; 3%Z; -4%Z; -1%Z; -1%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -4%Z; 3%Z; -4%Z] [2%Z; -1%Z; -2%Z; 4%Z; -3%Z; 0%Z; 0%Z; -5%Z; 8%Z; -7%Z; 10%Z; -9%Z; -3%Z; 4%Z; -3%Z].
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