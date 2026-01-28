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

(* Test case: input = [40000; 70000; 9999; 2; 60001; -10; 60000; -5; 7; 20000; 60000], output = [40001; 70001; 10000; 3; 60002; -9; 60001; -4; 8; 20001; 60001] *)
Example problem_42_example : problem_42_spec 
  [40000%Z; 70000%Z; 9999%Z; 2%Z; 60001%Z; -10%Z; 60000%Z; -5%Z; 7%Z; 20000%Z; 60000%Z] 
  [40001%Z; 70001%Z; 10000%Z; 3%Z; 60002%Z; -9%Z; 60001%Z; -4%Z; 8%Z; 20001%Z; 60001%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i as [|i]; [simpl; reflexivity | simpl in H]).
    lia.
Qed.