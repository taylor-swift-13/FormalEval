Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Definition check_prime_bool (p : nat) : bool :=
  (1 <? p) && forallb (fun d => negb (p mod d =? 0)) (seq 2 (p - 2)).

Lemma check_prime_correct : forall p, check_prime_bool p = true -> is_prime p.
Proof.
  intros p H.
  unfold check_prime_bool in H.
  apply andb_prop in H. destruct H as [Hgt Hdivs].
  apply Nat.ltb_lt in Hgt.
  split; [assumption|].
  intros d Hd.
  destruct (Nat.eq_dec d 1); [left; assumption|].
  destruct (Nat.eq_dec d p); [right; assumption|].
  assert (Hin: In d (seq 2 (p - 2))).
  {
    apply in_seq. split.
    - destruct d.
      + apply Nat.divide_0_l in Hd. subst. lia.
      + destruct d.
        * contradiction.
        * lia.
    - apply Nat.divide_pos_le in Hd; try lia.
      assert (d <> p) by assumption.
      lia.
  }
  rewrite forallb_forall in Hdivs.
  specialize (Hdivs d Hin).
  apply negb_true_iff in Hdivs.
  apply Nat.eqb_neq in Hdivs.
  exfalso. apply Hdivs.
  apply Nat.mod_divide; try lia.
  assumption.
Qed.

Example test_factorize_1207947 : factorize_spec 1207947 [3; 13; 47; 659].
Proof.
  unfold factorize_spec.
  split.
  - simpl. lia.
  - split.
    + repeat constructor; apply check_prime_correct; vm_compute; reflexivity.
    + repeat constructor; simpl; lia.
Qed.