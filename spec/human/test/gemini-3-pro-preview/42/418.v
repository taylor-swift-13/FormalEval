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

(* Test case: input = [-5; 18; 9; 14; -1; 9; -5], output = [-4; 19; 10; 15; 0; 10; -4] *)
Example problem_42_example : problem_42_spec [-5%Z; 18%Z; 9%Z; 14%Z; -1%Z; 9%Z; -5%Z] [-4%Z; 19%Z; 10%Z; 15%Z; 0%Z; 10%Z; -4%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    (* Check each index 0 through 6 *)
    repeat (destruct i as [|i]; [ simpl; reflexivity | ]).
    (* Handle out of bounds indices *)
    simpl in H.
    lia.
Qed.