Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_long_string :
  Spec "1WeeenWA man, a plans, a erStep osawn no hpetsecaisnral,  Panama.sLmxahinks" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros Hfalse.
    exfalso.
    specialize (Hfalse 0).
    assert (Hlen: (0 < (String.length "1WeeenWA man, a plans, a erStep osawn no hpetsecaisnral,  Panama.sLmxahinks") / 2)%nat).
    {
      simpl.
      unfold Nat.div.
      apply Nat.lt_0_succ.
    }
    apply Hfalse in Hlen.
    simpl in Hlen.
    discriminate Hlen.
Qed.