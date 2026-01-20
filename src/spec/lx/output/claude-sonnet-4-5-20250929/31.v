Require Import Arith.
Require Import Bool.
Require Import Lia.

Definition Spec (n : nat) (output : bool) : Prop :=
  (1 < n /\ (forall d : nat, d > 0 /\ d <= n /\ n mod d = 0 -> d = 1 \/ d = n)) <-> output = true.

Lemma mod_6_2 : 6 mod 2 = 0.
Proof.
  simpl. reflexivity.
Qed.

Lemma mod_6_3 : 6 mod 3 = 0.
Proof.
  simpl. reflexivity.
Qed.

Example test_is_prime_6 :
  Spec 6 false.
Proof.
  unfold Spec.
  split.
  - intro H.
    destruct H as [H_gt H_prime].
    exfalso.
    assert (H_2_div : 2 > 0 /\ 2 <= 6 /\ 6 mod 2 = 0).
    {
      split; [lia | split; [lia | apply mod_6_2]].
    }
    apply H_prime in H_2_div.
    destruct H_2_div as [H_eq_1 | H_eq_6].
    + lia.
    + lia.
  - intro H.
    discriminate H.
Qed.