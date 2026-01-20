Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "d3!@@@@2Zz213dd3!@@@2DoZz213!@@@2Zz21nama.oeman," false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert ((0 < (String.length "d3!@@@@2Zz213dd3!@@@2DoZz213!@@@2Zz21nama.oeman,") / 2)%nat) as Hi.
    {
      simpl.
      apply Nat.lt_0_succ.
    }
    specialize (H Hi).
    discriminate H.
Qed.