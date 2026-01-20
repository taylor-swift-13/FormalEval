Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_long_string :
  Spec "EvTaco cEvil is a name of a foeman, as I live.atil is a name ofoeman,as I live." false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < (String.length "EvTaco cEvil is a name of a foeman, as I live.atil is a name ofoeman,as I live." / 2)%nat) as Hi.
    { apply Nat.lt_0_succ. }
    specialize (H Hi).
    discriminate H.
Qed.