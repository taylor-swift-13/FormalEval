Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_long :
  Spec "Tacogeesea cEvil is a namf12zZ2@@@man,Ae of a foemplaWasan, as I live.a" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < (String.length "Tacogeesea cEvil is a namf12zZ2@@@man,Ae of a foemplaWasan, as I live.a" / 2)%nat) as Hi.
    {
      unfold String.length.
      simpl.
      apply Nat.lt_0_succ.
    }
    specialize (H Hi).
    discriminate H.
Qed.