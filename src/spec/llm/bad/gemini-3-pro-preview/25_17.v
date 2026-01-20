Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Definition check_prime (p : nat) : bool :=
  (1 <? p) && (forallb (fun d => negb (p mod d =? 0)) (seq 2 (p - 2))).

Lemma check_prime_correct : forall p, check_prime p = true -> is_prime p.
Proof.
  intros p H.
  unfold check_prime in H.
  apply andb_prop in H. destruct H as [H1 H2].
  apply Nat.ltb_lt in H1.
  unfold is_prime. split; [assumption|].
  intros d Hdiv.
  destruct (le_lt_dec d 1) as [Hle|Hgt].
  - destruct d.
    + destruct Hdiv as [x Hx]. rewrite Nat.mul_0_r in Hx. subst p. lia.
    + left. reflexivity.
  - destruct (le_lt_dec p d) as [Hle'|Hgt'].
    + apply Nat.divide_pos_le in Hdiv; [|lia]. right; lia.
    + rewrite forallb_forall in H2.
      assert (In d (seq 2 (p - 2))).
      { apply in_seq. split; lia. }
      specialize (H2 d H).
      apply negb_true_iff in H2.
      apply Nat.eqb_neq in H2.
      apply Nat.mod_divide in Hdiv; [|lia].
      contradiction.
Qed.

Example test_factorize_123456789 : factorize_spec 123456789 [3; 3; 3607; 3803].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat match goal with |- Forall _ _ => constructor end.
      all: try (apply check_prime_correct; vm_compute; reflexivity).
    + repeat constructor; try lia.
Qed.