Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

(* Pre: no special constraints for `is_palindrome` *)
Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example test_step_on_no_pets : problem_48_spec "step on no pets" true.
Proof.
  unfold problem_48_spec.
  split.
  - intros _.
    intros i H.
    simpl in *.
    destruct i; [reflexivity|].
    destruct i; [reflexivity|].
    destruct i; [reflexivity|].
    destruct i; [reflexivity|].
    destruct i; [reflexivity|].
    destruct i; [reflexivity|].
    destruct i; [reflexivity|].
    lia.
  - intros _.
    reflexivity.
Qed.