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

(* Auxiliary lemmas and functions for efficient primality testing *)

Lemma prime_sqrt_check : forall p,
  p > 1 ->
  (forall d, 2 <= d -> d * d <= p -> ~ Nat.divide d p) ->
  is_prime p.
Proof.
  intros p Hp Hsqrt.
  split; auto.
  intros d Hdiv.
  destruct (Nat.eq_dec d 1); [left; auto|].
  destruct (Nat.eq_dec d p); [right; auto|].
  assert (d <> 0). { intro; subst; destruct Hdiv; lia. }
  assert (2 <= d). { destruct d; try lia. destruct d; try lia. }
  destruct (le_lt_dec (d*d) p).
  - exfalso. apply (Hsqrt d); auto.
  - assert (exists k, p = d * k). { destruct Hdiv; exists x; rewrite Nat.mul_comm; auto. }
    destruct H0 as [k Hk].
    assert (k * d = p) as Hk'. { rewrite Nat.mul_comm; auto. }
    assert (k <> 0). { intro; subst; lia. }
    assert (k <> 1). { intro; subst; simpl in *; lia. }
    assert (k < d).
    { apply Nat.mul_lt_mono_pos_l with (p:=d); try lia.
      rewrite Hk'.
      rewrite Nat.mul_comm.
      apply Nat.lt_le_trans with (m:=d*d); auto. }
    assert (2 <= k). { destruct k; try lia. destruct k; try lia. }
    assert (k * k <= p).
    { apply Nat.mul_le_mono_nonneg_r with (n:=k) (m:=d) (p:=k) in H2; try lia.
      rewrite Hk' in H2. auto. }
    exfalso. apply (Hsqrt k); auto. exists d. rewrite Nat.mul_comm. auto.
Qed.

Fixpoint check_range (d p fuel : nat) : bool :=
  match fuel with
  | 0 => true 
  | S f => 
      match d * d <=? p with
      | false => true 
      | true => 
          match p mod d =? 0 with
          | true => false 
          | false => check_range (S d) p f
          end
      end
  end.

Lemma check_range_correct_aux : forall fuel d p,
  d <> 0 ->
  check_range d p fuel = true ->
  forall k, d <= k -> k < d + fuel -> k * k <= p -> ~ Nat.divide k p.
Proof.
  induction fuel; intros d p Hdnz Hres k Hdk Hfuel Hsq Hdiv.
  - lia.
  - simpl in Hres.
    destruct (d * d <=? p) eqn:Hbound.
    + destruct (p mod d =? 0) eqn:Hmod.
      * discriminate.
      * apply IHfuel with (k:=k) in Hres; try lia.
        destruct (Nat.eq_dec k d).
        -- subst. apply Nat.eqb_neq in Hmod. rewrite Nat.mod_divide in Hmod; auto.
        -- auto.
    + apply Nat.leb_gt in Hbound.
      assert (d * d > p) by auto.
      assert (d <= k) by auto.
      apply Nat.mul_le_mono_nonneg with (n:=d) (m:=k) (p:=d) (q:=k) in H1; try lia.
      lia.
Qed.

Lemma check_range_correct : forall p,
  check_range 2 p p = true ->
  (forall d, 2 <= d -> d * d <= p -> ~ Nat.divide d p).
Proof.
  intros p Hres d H2 Hsq Hdiv.
  apply check_range_correct_aux with (fuel:=p) (d:=2) (k:=d) in Hres; auto.
  lia.
Qed.

Ltac prove_prime :=
  apply prime_sqrt_check; 
  [ lia 
  | apply check_range_correct; 
    vm_compute; reflexivity ].

Example test_factorize_1073741788 : factorize_spec 1073741788 [2; 2; 7; 2341; 16381].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor; prove_prime.
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.