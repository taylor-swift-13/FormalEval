Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "d3!@@@2Z.z21nama.WAsnral,Dd3!f12zZ2@@@@!3j  d3!@@@2Zz21oeman,@@@2DoZz21o" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    exfalso.
    specialize (H 0).
    simpl in H.
    assert (0 < (String.length "d3!@@@2Z.z21nama.WAsnral,Dd3!f12zZ2@@@@!3j  d3!@@@2Zz21oeman,@@@2DoZz21o" / 2)%nat) as Hi by apply Nat.lt_0_succ.
    specialize (H Hi).
    simpl in H.
    discriminate.
Qed.