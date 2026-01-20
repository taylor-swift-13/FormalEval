Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "1212zZ2@@@@!@3Taco notj  d3!@@@2DoZz21zZ2@@@@!3Taco" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    exfalso.
    inversion H.
  - intros H.
    specialize (H 0).
    assert (0 < (String.length "1212zZ2@@@@!@3Taco notj  d3!@@@2DoZz21zZ2@@@@!3Taco" / 2)%nat) as Hi.
    { simpl. apply Nat.lt_0_succ. }
    pose proof (H Hi).
    simpl in H0.
    discriminate.
Qed.