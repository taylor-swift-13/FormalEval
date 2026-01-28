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

(* Test case: input = [-40; 80000; 90000; 21; -3; 14; 18; -2; 87], output = [-39; 80001; 90001; 22; -2; 15; 19; -1; 88] *)
Example problem_42_example : problem_42_spec [-40%Z; 80000%Z; 90000%Z; 21%Z; -3%Z; 14%Z; 18%Z; -2%Z; 87%Z] [-39%Z; 80001%Z; 90001%Z; 22%Z; -2%Z; 15%Z; 19%Z; -1%Z; 88%Z].
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