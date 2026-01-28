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

(* Test case: input = [20000; ...], output = [20001; ...] *)
Example problem_42_example : problem_42_spec 
  [20000%Z; 10000%Z; 40000%Z; 70000%Z; 9999%Z; 2%Z; 60001%Z; 100000%Z; 60000%Z; -6%Z; 20000%Z; 60000%Z] 
  [20001%Z; 10001%Z; 40001%Z; 70001%Z; 10000%Z; 3%Z; 60002%Z; 100001%Z; 60001%Z; -5%Z; 20001%Z; 60001%Z].
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [ simpl; reflexivity | simpl in H ]).
    lia.
Qed.