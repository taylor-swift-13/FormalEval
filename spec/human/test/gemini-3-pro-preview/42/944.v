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

(* Test case: input = [10000; 30000; 20000; 30000; 40000; 90000; 60000; 70000; 12; 90000], output = [10001; 30001; 20001; 30001; 40001; 90001; 60001; 70001; 13; 90001] *)
Example problem_42_example : problem_42_spec 
  [10000; 30000; 20000; 30000; 40000; 90000; 60000; 70000; 12; 90000] 
  [10001; 30001; 20001; 30001; 40001; 90001; 60001; 70001; 13; 90001].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i as [|i]; [simpl; reflexivity | simpl in H]).
    lia.
Qed.