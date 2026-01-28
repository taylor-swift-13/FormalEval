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

(* Test case: input = [90000; 4; 8; -29; 79999; 16; 20; 10; 79999], output = [90001; 5; 9; -28; 80000; 17; 21; 11; 80000] *)
Example problem_42_example : problem_42_spec 
  [90000%Z; 4%Z; 8%Z; -29%Z; 79999%Z; 16%Z; 20%Z; 10%Z; 79999%Z] 
  [90001%Z; 5%Z; 9%Z; -28%Z; 80000%Z; 17%Z; 21%Z; 11%Z; 80000%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i; [simpl; reflexivity | ]).
    simpl in H.
    lia.
Qed.