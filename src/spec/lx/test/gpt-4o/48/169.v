Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "A man, a plan, a erecaisnral,  Pa12zZ2@@@@!@3Taco notj  d3!@@@2Zz21nama." false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    assert (0 < (String.length "A man, a plan, a erecaisnral,  Pa12zZ2@@@@!@3Taco notj  d3!@@@2Zz21nama." / 2)%nat) as Hi.
    {
      simpl.
      unfold lt.
      apply Nat.lt_0_succ.
    }
    apply H in Hi.
    simpl in Hi.
    discriminate Hi.
Qed.