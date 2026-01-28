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

(* Test case: input = [2; -2; 3; 3; -4; 5; 6; -6; -8; 9; -10; 9], output = [3; -1; 4; 4; -3; 6; 7; -5; -7; 10; -9; 10] *)
Example problem_42_example : problem_42_spec [2; -2; 3; 3; -4; 5; 6; -6; -8; 9; -10; 9]%Z [3; -1; 4; 4; -3; 6; 7; -5; -7; 10; -9; 10]%Z.
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    (* We destruct i for each element in the list (length 12) *)
    do 12 (destruct i; [ simpl; reflexivity | ]).
    (* Handle out of bounds *)
    simpl in H.
    lia.
Qed.