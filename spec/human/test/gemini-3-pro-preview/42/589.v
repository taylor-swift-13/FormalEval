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

(* Test case: input = [2; -7; 4; 6; 80000; 5; 100000; 12; 14; 16; 18; 0; 20; 2], output = [3; -6; 5; 7; 80001; 6; 100001; 13; 15; 17; 19; 1; 21; 3] *)
Example problem_42_example : problem_42_spec 
  [2%Z; -7%Z; 4%Z; 6%Z; 80000%Z; 5%Z; 100000%Z; 12%Z; 14%Z; 16%Z; 18%Z; 0%Z; 20%Z; 2%Z] 
  [3%Z; -6%Z; 5%Z; 7%Z; 80001%Z; 6%Z; 100001%Z; 13%Z; 15%Z; 17%Z; 19%Z; 1%Z; 21%Z; 3%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    (* We destruct i for each element in the list. *)
    repeat (destruct i as [|i]; [ simpl; reflexivity | ]).
    (* After checking all elements, the remaining index is out of bounds *)
    simpl in H.
    lia.
Qed.