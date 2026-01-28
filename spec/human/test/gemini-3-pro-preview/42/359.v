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

(* Test case: input = [1; -2; 3; -4; 40000; 12; 9; -10], output = [2; -1; 4; -3; 40001; 13; 10; -9] *)
Example problem_42_example : problem_42_spec [1%Z; -2%Z; 3%Z; -4%Z; 40000%Z; 12%Z; 9%Z; -10%Z] [2%Z; -1%Z; 4%Z; -3%Z; 40001%Z; 13%Z; 10%Z; -9%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    (* Iterate through indices 0 to 7 *)
    repeat (destruct i as [|i]; [simpl; reflexivity | simpl in H]).
    (* Indices >= 8 are out of bounds *)
    lia.
Qed.