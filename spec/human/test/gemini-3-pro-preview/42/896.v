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

(* Test case: input = [10000; 20000; ...], output = [10001; 20001; ...] *)
Example problem_42_example : problem_42_spec 
  [10000%Z; 20000%Z; 30000%Z; 7%Z; 2%Z; 40000%Z; 60000%Z; 80000%Z; 2%Z; 100002%Z; -1%Z; 2%Z; 2%Z] 
  [10001%Z; 20001%Z; 30001%Z; 8%Z; 3%Z; 40001%Z; 60001%Z; 80001%Z; 3%Z; 100003%Z; 0%Z; 3%Z; 3%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i as [|i]; [simpl; reflexivity | simpl in H]).
    (* Handle the out of bounds case *)
    lia.
Qed.