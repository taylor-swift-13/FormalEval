Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

(* Helper definitions and lemmas for primality checking *)

Lemma prime_sqrt_check : forall n,
  n > 1 ->
  (forall d, 2 <= d -> d * d <= n -> ~ Nat.divide d n) ->
  is_prime n.
Proof.
  intros n Hn Hcheck.
  split; auto.
  intros d Hdiv.
  destruct (Nat.eq_dec d 1); auto.
  destruct (Nat.eq_dec d n); auto.
  exfalso.
  assert (Hdn: 1 < d < n).
  { split.
    - destruct d; try lia. destruct d; try lia.
    - apply Nat.divide_pos_le in Hdiv; try lia.
      destruct Hdiv as [x Hx]. destruct x; try lia. destruct x; try lia.
      rewrite <- mult_n_Sm in Hx.
      assert (d * S (S x) > d * 1). apply Nat.mul_lt_mono_pos_l; lia.
      lia.
  }
  destruct Hdiv as [q Hq].
  assert (Hqn: 1 < q < n).
  {
    split.
    - destruct q; try lia. destruct q; try lia.
      rewrite Nat.mul_comm in Hq. rewrite Hq in Hdn.
      rewrite Nat.mul_1_l in Hdn. lia.
    - apply Nat.divide_pos_le; try lia.
      exists d. rewrite Nat.mul_comm. auto.
  }
  destruct (Nat.le_ge_cases d q).
  - apply (Hcheck d); try lia.
    apply Nat.le_trans with (m := d * q).
    apply Nat.mul_le_mono_l; auto.
    rewrite Hq. auto.
    exists q; auto.
  - apply (Hcheck q); try lia.
    apply Nat.le_trans with (m := q * d).
    apply Nat.mul_le_mono_l; auto.
    rewrite Nat.mul_comm. rewrite Hq. auto.
    exists d. rewrite Nat.mul_comm. auto.
Qed.

Fixpoint check_range (n d fuel : nat) : bool :=
  match fuel with
  | 0 => false
  | S f =>
    if d * d >? n then true
    else if Nat.eqb (n mod d) 0 then false
    else check_range n (S d) f
  end.

Lemma check_range_correct : forall n d fuel,
  d <> 0 ->
  check_range n d fuel = true ->
  forall k, d <= k -> k * k <= n -> ~ Nat.divide k n.
Proof.
  intros n d fuel. revert d. induction fuel.
  - intros d Zd H. discriminate.
  - intros d Zd H k Hdk Hkn Hdiv.
    simpl in H.
    destruct (d * d >? n) eqn:Hsq.
    + apply Nat.leb_gt in Hsq.
      assert (k < d).
      { destruct (le_gt_dec d k); try lia.
        apply Nat.mul_le_mono with (1:=l) (2:=l) in l.
        lia. }
      lia.
    + destruct (Nat.eqb (n mod d) 0) eqn:Hmod.
      * discriminate.
      * apply Nat.eqb_neq in Hmod.
        destruct (Nat.eq_dec k d).
        -- subst. apply Nat.mod_divide in Hdiv; try lia. contradiction.
        -- apply (IHfuel (S d)); try lia.
Qed.

Definition check_prime (n : nat) : bool :=
  if n <=? 1 then false
  else check_range n 2 n.

Lemma check_prime_correct : forall n, check_prime n = true -> is_prime n.
Proof.
  intros n H.
  unfold check_prime in H.
  destruct (n <=? 1) eqn:Hle; try discriminate.
  apply Nat.leb_nle in Hle.
  apply prime_sqrt_check; try lia.
  apply (check_range_correct n 2 n); try lia.
  assumption.
Qed.

Example test_factorize_new : 
  factorize_spec (N.to_nat 1003001000%N) [2; 2; 2; 5; 5; 5; 1003001].
Proof.
  unfold factorize_spec.
  split.
  - (* Product *)
    simpl. lia.
  - split.
    + (* Primality *)
      repeat constructor.
      * apply check_prime_correct. vm_compute. reflexivity.
      * apply check_prime_correct. vm_compute. reflexivity.
      * apply check_prime_correct. vm_compute. reflexivity.
      * apply check_prime_correct. vm_compute. reflexivity.
      * apply check_prime_correct. vm_compute. reflexivity.
      * apply check_prime_correct. vm_compute. reflexivity.
      * apply check_prime_correct. vm_compute. reflexivity.
    + (* Sorted *)
      repeat constructor; simpl; try lia.
Qed.