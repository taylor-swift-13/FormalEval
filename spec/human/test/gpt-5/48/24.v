Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_nonpalindrome :
  problem_48_spec "Was ait a car or a sacat I saw?" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hi.
    exfalso.
    discriminate H.
  - intros Hprop.
    exfalso.
    assert (Hlt: (0 < String.length "Was ait a car or a sacat I saw?" / 2)%nat) by (simpl; lia).
    specialize (Hprop 0 Hlt).
    simpl in Hprop.
    congruence.
Qed.