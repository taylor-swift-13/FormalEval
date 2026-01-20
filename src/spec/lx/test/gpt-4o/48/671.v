Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_as :
  Spec "as" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < 1)%nat by auto.
    apply H in H0.
    discriminate.
Qed.