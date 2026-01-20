Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_non_palindrome :
  Spec "A man, a plan, a canali.lve.a.tl, Panama." false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert ((0 < (String.length "A man, a plan, a canali.lve.a.tl, Panama.") / 2)%nat) as Hi.
    {
      simpl.
      apply Nat.lt_0_succ.
    }
    specialize (H Hi).
    simpl in H.
    discriminate H.
Qed.