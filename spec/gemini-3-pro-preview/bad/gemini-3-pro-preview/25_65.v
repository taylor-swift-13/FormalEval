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

Fixpoint check_range (n d fuel : nat) : bool :=
  match fuel with
  | 0 => true
  | S f => 
      if Nat.eqb (n mod d) 0 then false 
      else check_range n (S d) f
  end.

Lemma check_range_correct : forall n d fuel,
  d > 0 ->
  check_range n d fuel = true ->
  forall k, d <= k < d + fuel -> ~ Nat.divide k n.
Proof.
  induction fuel; intros d Hdpos Hcheck k Hk Hdiv.
  - lia.
  - simpl in Hcheck.
    destruct (Nat.eqb (n mod d) 0) eqn:Hmod.
    + discriminate.
    + destruct (Nat.eq_dec k d).
      * subst.
        apply Nat.mod_divide in Hdiv; try lia.
        rewrite Hdiv in Hmod. discriminate.
      * apply IHfuel with (k:=k) in Hcheck; try lia.
        apply Hcheck. auto.
Qed.

Lemma check_prime_correct : forall n,
  n > 1 ->
  check_range n 2 (n - 2) = true ->
  is_prime n.
Proof.
  intros n Hgt Hcheck.
  unfold is_prime. split; auto.
  intros d Hdiv.
  destruct (le_lt_dec d 1).
  - destruct d; try lia. left. auto.
  - destruct (Nat.eq_dec d n); auto.
    right. auto.
    exfalso.
    assert (2 <= d < 2 + (n - 2)) by lia.
    eapply check_range_correct in Hcheck; eauto.
    lia.
Qed.

Example test_factorize_112234368 : factorize_spec 112234368 [2; 2; 2; 2; 2; 2; 2; 3; 19; 15383].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat constructor.
      all: apply check_prime_correct; [lia | vm_compute; reflexivity].
    + repeat constructor; lia.
Qed.