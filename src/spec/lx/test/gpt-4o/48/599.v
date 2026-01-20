Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "f12zZ2@@@@!live12zZ2@@@@!3orTaco.a3j  d3!@@@2eZeman," false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert ((0 < (String.length "f12zZ2@@@@!live12zZ2@@@@!3orTaco.a3j  d3!@@@2eZeman,") / 2)%nat) as Hi.
    { apply Nat.lt_0_succ. }
    specialize (H Hi).
    simpl in H.
    discriminate H.
Qed.