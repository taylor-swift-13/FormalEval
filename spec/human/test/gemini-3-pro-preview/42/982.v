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

(* Test case: input = [2; 4; 7; 8; 10; 20000; 16; 18; 8; 4; 18], output = [3; 5; 8; 9; 11; 20001; 17; 19; 9; 5; 19] *)
Example problem_42_example : problem_42_spec [2; 4; 7; 8; 10; 20000; 16; 18; 8; 4; 18] [3; 5; 8; 9; 11; 20001; 17; 19; 9; 5; 19].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 11 (destruct i; [ simpl; reflexivity | ]).
    (* Handle out of bounds *)
    simpl in H.
    lia.
Qed.