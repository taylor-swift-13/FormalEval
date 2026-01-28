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

(* Test case: input = [9; 1; -29; -2; 3; 1; -4; -1; 5; 0; 40000; 9; 1; -10; 1; 9], output = ... *)
Example problem_42_example : problem_42_spec 
  [9%Z; 1%Z; -29%Z; -2%Z; 3%Z; 1%Z; -4%Z; -1%Z; 5%Z; 0%Z; 40000%Z; 9%Z; 1%Z; -10%Z; 1%Z; 9%Z] 
  [10%Z; 2%Z; -28%Z; -1%Z; 4%Z; 2%Z; -3%Z; 0%Z; 6%Z; 1%Z; 40001%Z; 10%Z; 2%Z; -9%Z; 2%Z; 10%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i; [ simpl; reflexivity | ]).
    simpl in H.
    lia.
Qed.