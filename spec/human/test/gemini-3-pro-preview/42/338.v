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

(* Test case: input = [-8; 5; 9; -2; true; 6; 5; 0; -1; -7; 3; false], output = [-7; 6; 10; -1; 2; 7; 6; 1; 0; -6; 4; 1] *)
(* Note: boolean 'true' is mapped to 1%Z and 'false' to 0%Z to match list Z type and output values *)
Example problem_42_example : problem_42_spec 
  [-8%Z; 5%Z; 9%Z; -2%Z; 1%Z; 6%Z; 5%Z; 0%Z; -1%Z; -7%Z; 3%Z; 0%Z] 
  [-7%Z; 6%Z; 10%Z; -1%Z; 2%Z; 7%Z; 6%Z; 1%Z; 0%Z; -6%Z; 4%Z; 1%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    (* We check each index individually *)
    repeat (destruct i; [ simpl; reflexivity | ]).
    (* Handle out of bounds *)
    simpl in H.
    lia.
Qed.