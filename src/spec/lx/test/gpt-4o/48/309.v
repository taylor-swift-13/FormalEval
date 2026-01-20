Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_non_palindrome :
  Spec "A man, a pl@@@@!33jan, geesea canala: Panama" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < (String.length "A man, a pl@@@@!33jan, geesea canala: Panama") / 2)%nat.
    { (* Proof that 0 is less than half the length of the string *)
      unfold String.length.
      simpl.
      apply Nat.lt_0_succ.
    }
    apply H in H0.
    simpl in H0.
    discriminate H0.
Qed.