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

(* Test case: input = [100000; ...], output = [100001; ...] *)
Example problem_42_example : problem_42_spec 
  [100000; 20000; 100000; 30000; 40000; 60000; 29999; 70000; 60001; 2; 100000; 60000; 60000] 
  [100001; 20001; 100001; 30001; 40001; 60001; 30000; 70001; 60002; 3; 100001; 60001; 60001].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i as [|i]; [simpl; reflexivity |]).
    simpl in H.
    lia.
Qed.