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

(* Test case: input = [-1; 0; -4; -4; -5; -4; -4], output = [0; 1; -3; -3; -4; -3; -3] *)
Example problem_42_example : problem_42_spec [-1%Z; 0%Z; -4%Z; -4%Z; -5%Z; -4%Z; -4%Z] [0%Z; 1%Z; -3%Z; -3%Z; -4%Z; -3%Z; -3%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    (* Verify for each index 0 to 6 *)
    repeat (destruct i as [|i]; [simpl; reflexivity | simpl in H]).
    (* Out of bounds *)
    lia.
Qed.