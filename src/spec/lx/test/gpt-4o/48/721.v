Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "T12zZ2Panama21acoDoe see 12zZ2@@j@@!j3jd3!@z@@2Zz2lieveA man, a plan,Elba. Pa cacnal, Pana.ma..1Go" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < (String.length "T12zZ2Panama21acoDoe see 12zZ2@@j@@!j3jd3!@z@@2Zz2lieveA man, a plan,Elba. Pa cacnal, Pana.ma..1Go" / 2)%nat) as Hi.
    { apply Nat.lt_0_succ. }
    specialize (H Hi).
    discriminate H.
Qed.