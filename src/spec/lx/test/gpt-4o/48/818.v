Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "Step12zZ2psaw?12@zZ2@@@@!3j  nama21ets@@@@!3j  12zZ2it@@2A man., wsaAeNAa plan, Pa  Pana.ma.Zz21" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < (String.length "Step12zZ2psaw?12@zZ2@@@@!3j  nama21ets@@@@!3j  12zZ2it@@2A man., wsaAeNAa plan, Pa  Pana.ma.Zz21") / 2)%nat as Hi.
    { unfold lt. apply Nat.lt_0_succ. }
    specialize (H Hi).
    simpl in H.
    discriminate H.
Qed.