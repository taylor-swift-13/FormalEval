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

(* Test case: input = [-5; 9; 20000; 9], output = [-4; 10; 20001; 10] *)
Example problem_42_example : problem_42_spec [-5%Z; 9%Z; 20000%Z; 9%Z] [-4%Z; 10%Z; 20001%Z; 10%Z].
Proof.
  unfold problem_42_spec.
  split.
  - (* Check length equality *)
    simpl.
    reflexivity.
  - (* Check elements constraint *)
    intros i H.
    (* i = 0 *)
    destruct i as [|i].
    { simpl. reflexivity. }
    (* i = 1 *)
    destruct i as [|i].
    { simpl. reflexivity. }
    (* i = 2 *)
    destruct i as [|i].
    { simpl. reflexivity. }
    (* i = 3 *)
    destruct i as [|i].
    { simpl. reflexivity. }
    (* i >= 4, contradiction with length *)
    simpl in H.
    lia.
Qed.