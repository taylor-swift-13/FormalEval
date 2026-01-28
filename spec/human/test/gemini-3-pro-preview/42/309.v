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

(* Test case: input = [1; -2; 80000; 3; -4; 7; 40000; 9; -10; 7; 7], output = [2; -1; 80001; 4; -3; 8; 40001; 10; -9; 8; 8] *)
Example problem_42_example : problem_42_spec [1%Z; -2%Z; 80000%Z; 3%Z; -4%Z; 7%Z; 40000%Z; 9%Z; -10%Z; 7%Z; 7%Z] [2%Z; -1%Z; 80001%Z; 4%Z; -3%Z; 8%Z; 40001%Z; 10%Z; -9%Z; 8%Z; 8%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 11 (destruct i; [simpl; reflexivity | simpl in H]).
    lia.
Qed.