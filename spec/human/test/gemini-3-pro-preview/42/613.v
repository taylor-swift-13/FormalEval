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

(* Test case: input = [-5; 0; 5; -10; 20; -30], output = [-4; 1; 6; -9; 21; -29] *)
Example problem_42_example : problem_42_spec [-5%Z; 0%Z; 5%Z; -10%Z; 20%Z; -30%Z] [-4%Z; 1%Z; 6%Z; -9%Z; 21%Z; -29%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 6 (destruct i; [ simpl; reflexivity | ]).
    simpl in H.
    lia.
Qed.