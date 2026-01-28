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

(* Test case: input = [-5; -4; -3; 8; -2; 9999; -1; -3; 30000; -3], output = [-4; -3; -2; 9; -1; 10000; 0; -2; 30001; -2] *)
Example problem_42_example : problem_42_spec [-5%Z; -4%Z; -3%Z; 8%Z; -2%Z; 9999%Z; -1%Z; -3%Z; 30000%Z; -3%Z] [-4%Z; -3%Z; -2%Z; 9%Z; -1%Z; 10000%Z; 0%Z; -2%Z; 30001%Z; -2%Z].
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