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

(* Test case: input = [80000; -2; 3; -4; 40000; 12; 9; -10], output = [80001; -1; 4; -3; 40001; 13; 10; -9] *)
Example problem_42_example : problem_42_spec [80000; -2; 3; -4; 40000; 12; 9; -10] [80001; -1; 4; -3; 40001; 13; 10; -9].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    (* Verify each element index by index *)
    do 8 (destruct i; [ simpl; reflexivity | ]).
    (* Handle out of bounds *)
    simpl in H.
    lia.
Qed.