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

(* Test case: input = [-2; 3; -1; 6; 0; 10; 20; -5; 1; -2; -7; 3; 10; 10], output = [-1; 4; 0; 7; 1; 11; 21; -4; 2; -1; -6; 4; 11; 11] *)
Example problem_42_example : problem_42_spec 
  [-2; 3; -1; 6; 0; 10; 20; -5; 1; -2; -7; 3; 10; 10] 
  [-1; 4; 0; 7; 1; 11; 21; -4; 2; -1; -6; 4; 11; 11].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    (* We destruct i for each element in the list to verify the property pointwise *)
    repeat (destruct i; [ simpl; reflexivity | ]).
    (* After checking all elements, the remaining case is out of bounds, implying contradiction *)
    simpl in H.
    lia.
Qed.