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

(* Helper definitions and lemmas for efficient primality checking via reflection *)

Fixpoint check_range (d n fuel : nat) : bool :=
  match fuel with
  | 0 => false
  | S f =>
    if d * d >? n then true
    else if n mod d =? 0 then false
    else check_range (S d) n f
  end.

Lemma check_range_correct : forall fuel d n,
  check_range d n fuel = true ->
  (forall k, d <= k -> k * k <= n -> ~ Nat.divide k n).
Proof.
  induction fuel; intros d n Hres k Hdk Hksq Hdiv.
  - discriminate.
  - simpl in Hres.
    destruct (d * d >? n) eqn:Hsq.
    + apply Nat.leb_gt in Hsq.
      assert (k < d).
      { destruct (le_lt_dec d k); auto.
        apply Nat.mul_le_mono_pos_l with (p:=k) in l; try lia.
        assert (d*d <= d*k). apply Nat.mul_le_mono_r. auto.
        lia. }
      lia.
    + destruct (n mod d =? 0) eqn:Hrem.
      * discriminate.
      * apply IHfuel in Hres; auto.
        -- apply Nat.eqb_neq in Hrem.
           destruct (Nat.eq_dec k d).
           ++ subst. intro. apply Hrem. apply Nat.mod_divide; try lia. auto.
           ++ apply Hres; auto. lia.
Qed.

Lemma divide_sqr_le : forall n d, 
  1 < n -> Nat.divide d n -> 1 < d < n -> 
  d * d <= n \/ (n / d) * (n / d) <= n.
Proof.
  intros n d Hn Hdiv Hbounds.
  destruct Hdiv as [k Hk].
  assert (Hk0 : k * d = n) by (rewrite Nat.mul_comm; auto).
  assert (Hk_pos : k <> 0). { intro. subst. lia. }
  assert (Hk_val : k = n / d). { symmetry. apply Nat.div_unique_exact; auto. }
  subst k.
  destruct (le_lt_dec d (n / d)).
  - left. rewrite <- Hk0. apply Nat.mul_le_mono_l. auto.
  - right. rewrite <- Hk0. rewrite Nat.mul_comm. apply Nat.mul_le_mono_l. lia.
Qed.

Lemma prime_test_sqrt : forall n,
  1 < n ->
  (forall d, 2 <= d -> d * d <= n -> ~ Nat.divide d n) ->
  is_prime n.
Proof.
  intros n Hn Hcheck.
  split; auto.
  intros d Hdiv.
  destruct (Nat.eq_dec d 1); auto.
  destruct (Nat.eq_dec d n); auto.
  exfalso.
  assert (1 < d < n).
  { split. 
    - destruct d; try lia. destruct d; try lia. auto.
    - apply Nat.divide_pos_le in Hdiv; try lia.
      destruct Hdiv. auto. contradiction.
  }
  apply divide_sqr_le in Hdiv; auto.
  destruct Hdiv.
  - apply (Hcheck d); auto. lia.
  - set (k := n / d).
    assert (Hdivk : Nat.divide k n).
    { exists d. rewrite Nat.mul_comm. apply Nat.div_exact; auto. 
      intro. subst. lia. }
    assert (2 <= k).
    { destruct k; try lia. destruct k; try lia.
      assert (n / d = 0 \/ n / d = 1) by lia.
      destruct H2.
      - apply Nat.div_small_iff in H2; try lia.
      - apply Nat.div_1_iff in H2; try lia. subst. lia.
    }
    apply (Hcheck k); auto.
Qed.

Definition is_prime_bool (n : nat) : bool :=
  if n <=? 1 then false
  else check_range 2 n n.

Lemma is_prime_bool_spec : forall n, is_prime_bool n = true -> is_prime n.
Proof.
  intros n H.
  unfold is_prime_bool in H.
  destruct (n <=? 1) eqn:Hle. discriminate.
  apply Nat.leb_gt in Hle.
  apply prime_test_sqrt; auto.
  intros d Hd2 Hsq.
  apply (check_range_correct n 2 n); auto.
Qed.

Example test_factorize_112234370 : factorize_spec 112234370 [2; 5; 11223437].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor.
      * apply is_prime_bool_spec. vm_compute. reflexivity.
      * apply is_prime_bool_spec. vm_compute. reflexivity.
      * apply is_prime_bool_spec. vm_compute. reflexivity.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.