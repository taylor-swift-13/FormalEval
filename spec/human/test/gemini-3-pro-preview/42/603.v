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

(* Test case: input = [-2; 6; 0; 10; -5; -6; 0; -2; -1; -7; 10], output = [-1; 7; 1; 11; -4; -5; 1; -1; 0; -6; 11] *)
Example problem_42_example : problem_42_spec [-2%Z; 6%Z; 0%Z; 10%Z; -5%Z; -6%Z; 0%Z; -2%Z; -1%Z; -7%Z; 10%Z] [-1%Z; 7%Z; 1%Z; 11%Z; -4%Z; -5%Z; 1%Z; -1%Z; 0%Z; -6%Z; 11%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 11 (destruct i; [simpl; reflexivity | ]).
    simpl in H.
    lia.
Qed.