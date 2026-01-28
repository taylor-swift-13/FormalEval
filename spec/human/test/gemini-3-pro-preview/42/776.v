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

(* Test case: input = [20000; 20000; 7; 18; 30000; 40000; 50000; 11; 80000; 90000; 100000], output = [20001; 20001; 8; 19; 30001; 40001; 50001; 12; 80001; 90001; 100001] *)
Example problem_42_example : problem_42_spec [20000%Z; 20000%Z; 7%Z; 18%Z; 30000%Z; 40000%Z; 50000%Z; 11%Z; 80000%Z; 90000%Z; 100000%Z] [20001%Z; 20001%Z; 8%Z; 19%Z; 30001%Z; 40001%Z; 50001%Z; 12%Z; 80001%Z; 90001%Z; 100001%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i as [|i]; [ simpl; reflexivity | ]).
    simpl in H.
    lia.
Qed.