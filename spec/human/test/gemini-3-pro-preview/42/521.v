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

(* Test case: input = [10000; 4; 6; 8; 10; 14; 16; 18], output = [10001; 5; 7; 9; 11; 15; 17; 19] *)
Example problem_42_example : problem_42_spec [10000%Z; 4%Z; 6%Z; 8%Z; 10%Z; 14%Z; 16%Z; 18%Z] [10001%Z; 5%Z; 7%Z; 9%Z; 11%Z; 15%Z; 17%Z; 19%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    (* Unroll the loop for fixed length list *)
    do 8 (destruct i; [ simpl; reflexivity | ]).
    (* Handle out of bounds *)
    simpl in H.
    lia.
Qed.