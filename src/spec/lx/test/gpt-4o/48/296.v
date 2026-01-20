Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_long :
  Spec "12zZ2@@@@!@3Taco notj  d3!@@@2DoZz2112zZ2@@@@!@3Taco notj  d3!@@@2DoZz212Zz21oeman," false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exfalso.
    assert (String.get 0 "12zZ2@@@@!@3Taco notj  d3!@@@2DoZz2112zZ2@@@@!@3Taco notj  d3!@@@2DoZz212Zz21oeman," <>
            String.get (String.length "12zZ2@@@@!@3Taco notj  d3!@@@2DoZz2112zZ2@@@@!@3Taco notj  d3!@@@2DoZz212Zz21oeman," - 1)
            "12zZ2@@@@!@3Taco notj  d3!@@@2DoZz2112zZ2@@@@!@3Taco notj  d3!@@@2DoZz212Zz21oeman,").
    {
      simpl.
      discriminate.
    }
    specialize (H 0).
    assert (0 < (String.length "12zZ2@@@@!@3Taco notj  d3!@@@2DoZz2112zZ2@@@@!@3Taco notj  d3!@@@2DoZz212Zz21oeman," / 2)%nat) as Hi.
    {
      simpl.
      apply Nat.lt_0_succ.
    }
    apply H in Hi.
    contradiction.
Qed.