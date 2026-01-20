Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "cEviiA man, a plaWas it sawa car o r a d3!@@@Tacocat I petssaw?n, a erecaisnral,  Panama.Panamalnot" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    exfalso.
    inversion H.
  - intros H.
    exfalso.
    specialize (H 0).
    assert (0 < (String.length "cEviiA man, a plaWas it sawa car o r a d3!@@@Tacocat I petssaw?n, a erecaisnral,  Panama.Panamalnot" / 2)%nat) as Hi.
    {
      simpl.
      apply Nat.lt_0_succ.
    }
    specialize (H Hi).
    discriminate.
Qed.