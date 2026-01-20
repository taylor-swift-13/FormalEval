Require Import Arith.
Require Import Lia.

Definition Spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Lemma mod_1_eq_0 : forall n : nat, n > 0 -> n mod 1 = 0.
Proof.
  intros n H.
  apply Nat.mod_1_r.
Qed.

Example test_largest_divisor_3 :
  Spec 3 1.
Proof.
  unfold Spec.
  split.
  - apply mod_1_eq_0.
    lia.
  - split.
    + lia.
    + intros i [H_pos H_lt] H_div.
      assert (H_i_cases : i = 1 \/ i = 2) by lia.
      destruct H_i_cases as [H_eq_1 | H_eq_2].
      * rewrite H_eq_1. lia.
      * rewrite H_eq_2 in H_div.
        simpl in H_div.
        discriminate H_div.
Qed.