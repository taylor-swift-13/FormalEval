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

(* Test case: input = [3; -1; 6; -1; 10; 19; -5; 9; 0; -2; -7], output = [4; 0; 7; 0; 11; 20; -4; 10; 1; -1; -6] *)
Example problem_42_example : problem_42_spec [3%Z; -1%Z; 6%Z; -1%Z; 10%Z; 19%Z; -5%Z; 9%Z; 0%Z; -2%Z; -7%Z] [4%Z; 0%Z; 7%Z; 0%Z; 11%Z; 20%Z; -4%Z; 10%Z; 1%Z; -1%Z; -6%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    (* Destruct i repeatedly to check each index 0..10 *)
    repeat (destruct i; [ simpl; reflexivity | ]).
    (* Handle out of bounds indices *)
    simpl in H.
    lia.
Qed.