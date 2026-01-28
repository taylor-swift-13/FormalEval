Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

(* Pre: no special constraints for `is_palindrome` *)
Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example test_zbcd : problem_48_spec "zbcd" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    simpl in H.
    specialize (H 0).
    simpl in H.
    assert (H0 : (0 < 2)%nat) by lia.
    specialize (H H0).
    discriminate H.
Qed.