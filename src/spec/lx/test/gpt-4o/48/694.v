Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_non_palindrome :
  Spec "12zZ21" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 2).
    assert (2 < (String.length "12zZ21") / 2)%nat.
    {
      simpl.
      compute.
      auto.
    }
    apply H in H0.
    simpl in H0.
    compute in H0.
    discriminate H0.
Qed.