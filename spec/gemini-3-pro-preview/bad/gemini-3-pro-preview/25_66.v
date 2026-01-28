Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

(* Helper: Trial division primality check *)
Fixpoint check_divs (d limit n : nat) : bool :=
  match limit with
  | 0 => true
  | S k => 
    if n mod d =? 0 then false
    else check_divs (S d) k n
  end.

Lemma check_divs_ok : forall limit d n,
  check_divs d limit n = true ->
  forall k, d <= k -> k < d + limit -> ~ Nat.divide k n.
Proof.
  induction limit; simpl; intros.
  - lia.
  - destruct (n mod d =? 0) eqn:Heq.
    + discriminate.
    + apply Nat.eqb_neq in Heq.
      destruct (Nat.eq_dec k d).
      * subst. intro C. apply Nat.mod_divide in C; try lia. congruence.
      * apply IHlimit with (k:=k); auto; lia.
Qed.

Definition is_prime_bool (n : nat) : bool :=
  if n <=? 1 then false
  else check_divs 2 (n - 2) n.

Lemma is_prime_bool_ok : forall n,
  is_prime_bool n = true -> is_prime n.
Proof.
  unfold is_prime_bool, is_prime. intros n H.
  destruct (n <=? 1) eqn:Hle.
  - discriminate.
  - apply Nat.leb_gt in Hle. split; auto.
    intros d Hdiv.
    assert (d = 1 \/ (1 < d < n) \/ d = n) by lia.
    destruct H0 as [? | [[? ?] | ?]]; auto.
    exfalso.
    apply check_divs_ok with (limit := n - 2) (d := 2) (n := n) (k := d) in H; try lia.
    apply H. auto.
Qed.

(* Helper: Equality via Z to avoid large nat construction *)
Lemma eq_nat_via_Z : forall n z, (0 <= z)%Z -> Z.of_nat n = z -> n = Z.to_nat z.
Proof.
  intros n z Hz H.
  rewrite <- H.
  rewrite Z2Nat.id; auto.
  apply Zle_0_nat.
Qed.

Example test_factorize_9999999965 : factorize_spec (Z.to_nat 9999999965%Z) [5; 29; 1327; 51971].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    apply eq_nat_via_Z.
    + lia.
    + Opaque mult.
      simpl. (* Unfolds fold_right *)
      rewrite !Nat2Z.inj_mul.
      vm_compute. reflexivity.
      Transparent mult.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor; apply is_prime_bool_ok; vm_compute; reflexivity.
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.