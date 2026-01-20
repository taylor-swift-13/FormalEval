Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_non_empty :
  Spec "eNO" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    assert (String.get 0 "eNO" <> String.get (String.length "eNO" - 1 - 0) "eNO").
    + simpl. discriminate.
    + specialize (H 0 ltac:(simpl; auto)).
      contradiction.
Qed.