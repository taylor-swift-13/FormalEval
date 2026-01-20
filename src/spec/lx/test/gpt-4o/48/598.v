Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "cEcvilcd3!@@@2 ord3!a@@@2Zz21oeman,Able wliveas I ere I saw Elba.name1" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < (String.length "cEcvilcd3!@@@2 ord3!a@@@2Zz21oeman,Able wliveas I ere I saw Elba.name1") / 2)%nat as Hi.
    { unfold lt. apply Nat.lt_0_succ. }
    specialize (H Hi).
    discriminate H.
Qed.