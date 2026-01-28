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

(* Test case: input = [-5; 12; 70000; -3; -3; -4; 0; 70000], output = [-4; 13; 70001; -2; -2; -3; 1; 70001] *)
Example problem_42_example : problem_42_spec [-5%Z; 12%Z; 70000%Z; -3%Z; -3%Z; -4%Z; 0%Z; 70000%Z] [-4%Z; 13%Z; 70001%Z; -2%Z; -2%Z; -3%Z; 1%Z; 70001%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    (* Check for indices 0 to 7 *)
    do 8 (destruct i; [ simpl; reflexivity | ]).
    (* Out of bounds *)
    simpl in H.
    lia.
Qed.