Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_long :
  Spec "EvTaco cEvil is a name of a foeman, as I live.atil is a nam12zZ2@@@@!3Taco noca?ttj  d3!parssaw?@@@2Zz21e ofoeman, as I live.Tacat" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    assert (0 < (String.length "EvTaco cEvil is a name of a foeman, as I live.atil is a nam12zZ2@@@@!3Taco noca?ttj  d3!parssaw?@@@2Zz21e ofoeman, as I live.Tacat" / 2)%nat) as Hi.
    {
      simpl.
      unfold lt.
      apply Nat.lt_0_succ.
    }
    apply H in Hi.
    simpl in Hi.
    discriminate Hi.
Qed.