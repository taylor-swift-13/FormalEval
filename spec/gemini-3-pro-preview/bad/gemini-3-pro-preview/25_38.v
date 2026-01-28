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

(* Helper definitions for efficient primality checking *)

Fixpoint check_range (d count n : nat) : bool :=
  match count with
  | 0 => true
  | S c => 
    if n mod d =? 0 then false else check_range (S d) c n
  end.

Lemma check_range_correct : forall count d n,
  check_range d count n = true ->
  forall k, d <= k < d + count -> ~ Nat.divide k n.
Proof.
  induction count; intros d n H k Hk Hdiv.
  - lia.
  - simpl in H.
    destruct (n mod d =? 0) eqn:Hrem.
    + discriminate.
    + destruct (Nat.eq_dec k d).
      * subst. apply Nat.mod_divide in Hdiv; [|lia]. rewrite Hrem in Hdiv. discriminate.
      * apply IHcount with (k:=k) in H; try lia.
Qed.

Lemma no_divisors_implies_prime : forall n bound,
  1 < n ->
  bound * bound > n ->
  (forall d, 2 <= d < bound -> ~ Nat.divide d n) ->
  is_prime n.
Proof.
  intros n bound Hn Hbound Hcheck.
  split; [assumption|].
  intros d Hdiv.
  destruct (Nat.eq_dec d 1); [left; assumption|].
  destruct (Nat.eq_dec d n); [right; assumption|].
  
  destruct Hdiv as [k Hk].
  assert (Hk_div: Nat.divide k n).
  { exists d. rewrite Nat.mul_comm. assumption. }
  
  assert (H_d_range: 1 < d < n).
  {
    split.
    - destruct d; [destruct Hdiv as [x Hx]; rewrite Nat.mul_0_r in Hx; discriminate|].
      destruct d; [contradiction|].
      lia.
    - apply Nat.divide_pos_le in Hdiv; [|lia].
      destruct (Nat.eq_dec d n); [contradiction|].
      assumption.
  }
  
  assert (H_k_range: 1 < k < n).
  {
     split.
     - destruct k.
       + rewrite Nat.mul_0_l in Hk. subst. lia.
       + destruct k.
         * rewrite Nat.mul_1_l in Hk. subst. lia.
         * lia.
     - apply Nat.divide_pos_le in Hk_div; [|lia].
       destruct (Nat.eq_dec k n).
       + subst. rewrite Nat.mul_comm in Hk. 
         assert (d = 1). { apply Nat.mul_id_l with (n:=n); auto. lia. }
         subst. lia.
       + assumption.
  }

  destruct (le_lt_dec bound d).
  - (* bound <= d *)
    assert (k < bound).
    {
       destruct (le_lt_dec bound k); [|assumption].
       assert (bound * bound <= n).
       {
         transitivity (k * bound).
         - apply Nat.mul_le_mono_r. assumption.
         - rewrite Nat.mul_comm in Hk. rewrite <- Hk.
           apply Nat.mul_le_mono_l. assumption.
       }
       lia.
    }
    assert (2 <= k < bound) by lia.
    exfalso. apply (Hcheck k); assumption.
  - (* d < bound *)
    assert (2 <= d < bound) by lia.
    exfalso. apply (Hcheck d); assumption.
Qed.

Lemma prime_31 : is_prime 31.
Proof.
  apply no_divisors_implies_prime with (bound := 6).
  - lia.
  - simpl. lia.
  - assert (H: check_range 2 4 31 = true) by (vm_compute; reflexivity).
    pose proof (check_range_correct 4 2 31 H).
    intros d Hd.
    apply H0.
    lia.
Qed.

Lemma prime_128467 : is_prime 128467.
Proof.
  apply no_divisors_implies_prime with (bound := 360).
  - lia.
  - simpl. lia.
  - assert (H: check_range 2 358 128467 = true) by (vm_compute; reflexivity).
    pose proof (check_range_correct 358 2 128467 H).
    intros d Hd.
    apply H0.
    lia.
Qed.

Example test_factorize_123456787 : factorize_spec 123456787 [31; 31; 128467].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * apply prime_31.
      * constructor.
        -- apply prime_31.
        -- constructor.
           ++ apply prime_128467.
           ++ constructor.
    + repeat constructor.
Qed.