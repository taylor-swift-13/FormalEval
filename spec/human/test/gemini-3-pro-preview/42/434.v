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

(* Test case: input = [5; 9; -9; 14; 6; 5; 0; -1; -8; 3], output = [6; 10; -8; 15; 7; 6; 1; 0; -7; 4] *)
Example problem_42_example : problem_42_spec [5%Z; 9%Z; -9%Z; 14%Z; 6%Z; 5%Z; 0%Z; -1%Z; -8%Z; 3%Z] [6%Z; 10%Z; -8%Z; 15%Z; 7%Z; 6%Z; 1%Z; 0%Z; -7%Z; 4%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 10 (destruct i; [ simpl; reflexivity | ]).
    simpl in H; lia.
Qed.