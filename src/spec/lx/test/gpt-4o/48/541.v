Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "Dd3!@@@212ozZ2@@@@A man, a plZan, a erecaisnral,  Pa12zZ2@@@@!@3Taco notj  d3!@@@2Zz21nama.!@3Taco 12zZ2@@@@!@3Taco2notj  d3!@@@2DoZz21DoZz21o" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < (String.length "Dd3!@@@212ozZ2@@@@A man, a plZan, a erecaisnral,  Pa12zZ2@@@@!@3Taco notj  d3!@@@2Zz21nama.!@3Taco 12zZ2@@@@!@3Taco2notj  d3!@@@2DoZz21DoZz21o") / 2)%nat as Hi by apply Nat.lt_0_succ.
    specialize (H Hi).
    discriminate.
Qed.