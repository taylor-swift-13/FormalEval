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

(* Test case: input = [1; 5; 6; 13; 8; -1; 20; 16; 14; 4; 67; 1; 7; 6], output = [2; 6; 7; 14; 9; 0; 21; 17; 15; 5; 68; 2; 8; 7] *)
Example problem_42_example : problem_42_spec 
  [1%Z; 5%Z; 6%Z; 13%Z; 8%Z; -1%Z; 20%Z; 16%Z; 14%Z; 4%Z; 67%Z; 1%Z; 7%Z; 6%Z] 
  [2%Z; 6%Z; 7%Z; 14%Z; 9%Z; 0%Z; 21%Z; 17%Z; 15%Z; 5%Z; 68%Z; 2%Z; 8%Z; 7%Z].
Proof.
  unfold problem_42_spec.
  split.
  - simpl.
    reflexivity.
  - intros i H.
    repeat (destruct i; [ simpl; reflexivity | ]).
    simpl in H.
    lia.
Qed.