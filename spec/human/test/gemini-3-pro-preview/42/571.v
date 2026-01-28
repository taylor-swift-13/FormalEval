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

(* Test case: input = [-5; 20000; -3; -7; -3; -29; 21; -5; -5; -5], output = [-4; 20001; -2; -6; -2; -28; 22; -4; -4; -4] *)
Example problem_42_example : problem_42_spec [-5%Z; 20000%Z; -3%Z; -7%Z; -3%Z; -29%Z; 21%Z; -5%Z; -5%Z; -5%Z] [-4%Z; 20001%Z; -2%Z; -6%Z; -2%Z; -28%Z; 22%Z; -4%Z; -4%Z; -4%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i as [|i]; [simpl; reflexivity | ]).
    simpl in H.
    lia.
Qed.