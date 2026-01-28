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

(* Test case: input = [-2; 3; -1; 90001; 0; 10; 20; -5; 1; -2; -7; 10; 3; 10; 10], output = [-1; 4; 0; 90002; 1; 11; 21; -4; 2; -1; -6; 11; 4; 11; 11] *)
Example problem_42_example : problem_42_spec [-2%Z; 3%Z; -1%Z; 90001%Z; 0%Z; 10%Z; 20%Z; -5%Z; 1%Z; -2%Z; -7%Z; 10%Z; 3%Z; 10%Z; 10%Z] [-1%Z; 4%Z; 0%Z; 90002%Z; 1%Z; 11%Z; 21%Z; -4%Z; 2%Z; -1%Z; -6%Z; 11%Z; 4%Z; 11%Z; 11%Z].
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