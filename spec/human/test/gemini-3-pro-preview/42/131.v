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

(* Test case: input = [0; 1; 0; 1; 0; 1], output = [1; 2; 1; 2; 1; 2] *)
Example problem_42_example : problem_42_spec [0%Z; 1%Z; 0%Z; 1%Z; 0%Z; 1%Z] [1%Z; 2%Z; 1%Z; 2%Z; 1%Z; 2%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    repeat (destruct i as [|i]; [ simpl; reflexivity | ]).
    (* After checking all indices, the remaining case is out of bounds *)
    simpl in H.
    lia.
Qed.