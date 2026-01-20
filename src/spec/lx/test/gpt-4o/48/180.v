Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_on :
  Spec "on" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    assert (0 < (String.length "on" / 2)%nat).
    {
      simpl. unfold Nat.div. simpl. apply Nat.lt_0_1.
    }
    specialize (H H0).
    simpl in H.
    inversion H.
Qed.