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

(* Test case: input = [-3; 1; 4; 6; 8; 2; 10; 21; 14; 9; 16; 20; 20], output = [-2; 2; 5; 7; 9; 3; 11; 22; 15; 10; 17; 21; 21] *)
Example problem_42_example : problem_42_spec 
  [-3%Z; 1%Z; 4%Z; 6%Z; 8%Z; 2%Z; 10%Z; 21%Z; 14%Z; 9%Z; 16%Z; 20%Z; 20%Z] 
  [-2%Z; 2%Z; 5%Z; 7%Z; 9%Z; 3%Z; 11%Z; 22%Z; 15%Z; 10%Z; 17%Z; 21%Z; 21%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 13 (destruct i as [|i]; [ simpl; reflexivity | ]).
    simpl in H.
    lia.
Qed.