Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition Spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example is_palindrome_test_complex :
  Spec "A man,  plan, a canal: PanamTacA man,Taco cEvil i12zZ2@@@@!@3Tacos a name of a foeman, as I live.at a plan, geesea canal: Panamaa" false.
Proof.
  unfold Spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    exfalso.
    specialize (H 0%nat).
    simpl in H.
    assert (0 < (String.length "A man,  plan, a canal: PanamTacA man,Taco cEvil i12zZ2@@@@!@3Tacos a name of a foeman, as I live.at a plan, geesea canal: Panamaa") / 2)%nat as Hi.
    { apply Nat.lt_0_succ. }
    specialize (H Hi).
    discriminate.
Qed.