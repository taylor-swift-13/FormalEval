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

(* Test case: input = [6; 2; 20000; ...], output = [7; 3; 20001; ...] *)
Example problem_42_example : problem_42_spec 
  [6; 2; 20000; 49999; 30000; 40000; 50000; -6; 60000; 70000; 80000; 100000]
  [7; 3; 20001; 50000; 30001; 40001; 50001; -5; 60001; 70001; 80001; 100001].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    do 12 (destruct i; [ simpl; reflexivity | ]).
    simpl in H.
    lia.
Qed.