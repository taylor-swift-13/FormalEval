Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Compare_dec.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_was :
  Spec "was" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < (String.length "was") / 2)%nat.
    { compute. auto. }
    apply H in H0.
    simpl in H0.
    discriminate H0.
Qed.