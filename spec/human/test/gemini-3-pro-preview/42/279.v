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

(* Test case: input = [9; 1; -2; 3; 1; -4; -1; 5; 40000; 9; 1; -10; 1], output = [10; 2; -1; 4; 2; -3; 0; 6; 40001; 10; 2; -9; 2] *)
Example problem_42_example : problem_42_spec 
  [9; 1; -2; 3; 1; -4; -1; 5; 40000; 9; 1; -10; 1]%Z 
  [10; 2; -1; 4; 2; -3; 0; 6; 40001; 10; 2; -9; 2]%Z.
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 13 (destruct i; [simpl; reflexivity | ]).
    (* Out of bounds *)
    simpl in H.
    lia.
Qed.