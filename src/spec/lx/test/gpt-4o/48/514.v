Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_non_palindrome :
  Spec "PanPama" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0%nat).
    assert ((0 < (String.length "PanPama") / 2)%nat) as Hi.
    {
      simpl.
      compute.
      auto.
    }
    specialize (H Hi).
    simpl in H.
    discriminate H.
Qed.