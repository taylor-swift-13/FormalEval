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
  apply andb_prop in H. destruct H as [Hgt Hforall].
  apply Nat.ltb_lt in Hgt.
  unfold is_prime. split; [assumption|].
  intros d Hdiv.
  destruct (d =? 1) eqn:Ed1.
  - left. apply Nat.eqb_eq. assumption.
  - destruct (d =? p) eqn:Edp.
    + right. apply Nat.eqb_eq. assumption.
    + apply Nat.eqb_neq in Ed1.
      apply Nat.eqb_neq in Edp.
      assert (Hrange: 1 < d < p).
      {
        split.
        - destruct d.
          + destruct Hdiv as [x Hx]. rewrite Nat.mul_0_r in Hx. subst p. lia.
          + destruct d; lia.
        - apply Nat.divide_pos_le in Hdiv; lia.
      }
      assert (Hin: In d (seq 2 (p - 2))).
      {
        apply in_seq.
        split; [lia|].
        simpl. lia.
      }
      rewrite forallb_forall in Hforall.
      specialize (Hforall d Hin).
      apply negb_true_iff in Hforall.
      apply Nat.eqb_neq in Hforall.
      apply Nat.mod_divide in Hdiv; [|lia].
      contradiction.
Qed.

Example test_factorize_999978 : factorize_spec 999978 [2; 3; 7; 29; 821].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor; apply check_prime_correct; vm_compute; reflexivity.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.