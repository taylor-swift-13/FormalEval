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

Example problem_42_example : problem_42_spec [1; 4; 6; 8; 10; 10; 16; 18; 18; 20]%Z [2; 5; 7; 9; 11; 11; 17; 19; 19; 21]%Z.
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.