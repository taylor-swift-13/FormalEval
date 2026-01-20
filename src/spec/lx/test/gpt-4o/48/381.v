Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "eenWA man, a plan, a erStep osawn no pets12zZWas it a car or a cat Ia saw?ecaisnral,  Panama.sLmxahink" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < (String.length "eenWA man, a plan, a erStep osawn no pets12zZWas it a car or a cat Ia saw?ecaisnral,  Panama.sLmxahink" / 2)%nat) as Hi.
    { apply Nat.lt_0_succ. }
    specialize (H Hi).
    simpl in H.
    discriminate.
Qed.