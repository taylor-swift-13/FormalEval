Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_long_string :
  Spec "Tacogeese cEvil is ca namf12zZ2@@@man,Ae of a foeman, as I live.a" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    assert (0 < (String.length "Tacogeese cEvil is ca namf12zZ2@@@man,Ae of a foeman, as I live.a" / 2)%nat) as Hi.
    { simpl. apply Nat.lt_0_succ. }
    apply H in Hi.
    simpl in Hi.
    discriminate Hi.
Qed.