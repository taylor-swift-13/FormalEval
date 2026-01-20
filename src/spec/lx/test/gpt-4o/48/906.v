Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_non_palindrome :
  Spec "12zZas2@@j@@!j3jd3!@@@2fIoem,an,I" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert ((0 < (String.length "12zZas2@@j@@!j3jd3!@@@2fIoem,an,I") / 2)%nat).
    {
      simpl.
      apply Nat.lt_0_succ.
    }
    apply H in H0.
    simpl in H0.
    discriminate H0.
Qed.