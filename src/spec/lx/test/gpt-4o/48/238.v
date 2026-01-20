Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_non_palindrome :
  Spec "A man, a plan, a cananWA man, a plan, a erecaisnral,  Panama.sLmxhinkma" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    assert (0 < (String.length "A man, a plan, a cananWA man, a plan, a erecaisnral,  Panama.sLmxhinkma") / 2)%nat as Hi by apply Nat.lt_0_succ.
    simpl in Hi.
    apply H in Hi.
    simpl in Hi.
    discriminate Hi.
Qed.