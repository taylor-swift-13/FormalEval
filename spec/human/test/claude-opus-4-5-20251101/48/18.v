Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

(* Pre: no special constraints for `is_palindrome` *)
Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example test_bab : problem_48_spec "bab" true.
Proof.
  unfold problem_48_spec.
  split.
  - intros _.
    intros i H.
    simpl in H.
    assert (i = 0) by lia.
    subst i.
    simpl.
    reflexivity.
  - intros _.
    reflexivity.
Qed.