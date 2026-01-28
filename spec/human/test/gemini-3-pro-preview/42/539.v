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

(* Test case: input = [7; -5; 8; 9; -1; 9], output = [8; -4; 9; 10; 0; 10] *)
Example problem_42_example : problem_42_spec [7%Z; -5%Z; 8%Z; 9%Z; -1%Z; 9%Z] [8%Z; -4%Z; 9%Z; 10%Z; 0%Z; 10%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 6 (destruct i as [|i]; [simpl; reflexivity | ]).
    (* Since length is 6, i >= 6 is a contradiction *)
    simpl in H.
    lia.
Qed.