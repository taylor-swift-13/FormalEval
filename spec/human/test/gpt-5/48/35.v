Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_abcaabca :
  problem_48_spec "abcaabca" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hi.
    exfalso.
    discriminate H.
  - intros H.
    exfalso.
    assert ((1 < String.length "abcaabca" / 2)%nat) by (simpl; lia).
    specialize (H 1 H0).
    simpl in H.
    congruence.
Qed.