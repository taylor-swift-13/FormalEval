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

(* Test case: input = [-8; 40000; 5; 9; -2; 6; 5; 0; -1; -8; 3; -1; 9], output = [-7; 40001; 6; 10; -1; 7; 6; 1; 0; -7; 4; 0; 10] *)
Example problem_42_example : problem_42_spec 
  [-8%Z; 40000%Z; 5%Z; 9%Z; -2%Z; 6%Z; 5%Z; 0%Z; -1%Z; -8%Z; 3%Z; -1%Z; 9%Z] 
  [-7%Z; 40001%Z; 6%Z; 10%Z; -1%Z; 7%Z; 6%Z; 1%Z; 0%Z; -7%Z; 4%Z; 0%Z; 10%Z].
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