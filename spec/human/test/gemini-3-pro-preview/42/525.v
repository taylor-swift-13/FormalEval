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

(* Test case: input = [-5; -4; 12; -3; -2; 0; -2; 20001; -1; -3], output = [-4; -3; 13; -2; -1; 1; -1; 20002; 0; -2] *)
Example problem_42_example : problem_42_spec [-5%Z; -4%Z; 12%Z; -3%Z; -2%Z; 0%Z; -2%Z; 20001%Z; -1%Z; -3%Z] [-4%Z; -3%Z; 13%Z; -2%Z; -1%Z; 1%Z; -1%Z; 20002%Z; 0%Z; -2%Z].
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.