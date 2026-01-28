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

(* Test case: input = [-78; -17; 90; 16; -35; -6; -8; 4; 49; 40001], output = [-77; -16; 91; 17; -34; -5; -7; 5; 50; 40002] *)
Example problem_42_example : problem_42_spec [-78%Z; -17%Z; 90%Z; 16%Z; -35%Z; -6%Z; -8%Z; 4%Z; 49%Z; 40001%Z] [-77%Z; -16%Z; 91%Z; 17%Z; -34%Z; -5%Z; -7%Z; 5%Z; 50%Z; 40002%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i as [|i]; [ simpl; reflexivity | simpl in H ]).
    lia.
Qed.