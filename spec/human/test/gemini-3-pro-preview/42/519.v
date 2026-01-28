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

(* Test case: input = [10000; ...], output = [10001; ...] *)
Example problem_42_example : problem_42_spec 
  [10000%Z; 20000%Z; -10%Z; 40000%Z; 15%Z; 70000%Z; 79999%Z; 90000%Z; 100000%Z] 
  [10001%Z; 20001%Z; -9%Z; 40001%Z; 16%Z; 70001%Z; 80000%Z; 90001%Z; 100001%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 9 (destruct i as [|i]; [simpl; reflexivity |]).
    simpl in H.
    lia.
Qed.