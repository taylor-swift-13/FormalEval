Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "A man, a plaWas it sawa car o r a cat I petssaw?n, a erecaisnral,  Panama.Panama" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < (String.length "A man, a plaWas it sawa car o r a cat I petssaw?n, a erecaisnral,  Panama.Panama") / 2)%nat.
    { 
      apply Nat.lt_0_succ.
    }
    apply H in H0.
    discriminate H0.
Qed.