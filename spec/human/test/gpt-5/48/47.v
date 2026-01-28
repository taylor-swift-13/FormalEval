Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_babbabcca :
  problem_48_spec "babbabcca" false.
Proof.
  unfold problem_48_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H.
    exfalso.
    assert (Elen : String.length "babbabcca" = 9%nat) by reflexivity.
    assert (Hlt : (0 < String.length "babbabcca" / 2)%nat).
    { rewrite Elen.
      assert (D : 9 / 2 = 4) by reflexivity.
      rewrite D; lia.
    }
    specialize (H 0 Hlt).
    cbn in H.
    discriminate H.
Qed.