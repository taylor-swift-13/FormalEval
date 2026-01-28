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

(* Auxiliary definitions and lemmas for primality checking *)

Fixpoint check_range (d : nat) (fuel : nat) (n : nat) : bool :=
  match fuel with
  | 0 => true
  | S fuel' =>
    if d * d >? n then true
    else if n mod d =? 0 then false
    else check_range (S d) fuel' n
  end.

Lemma check_range_sound : forall fuel d n,
  check_range d fuel n = true ->
  forall k, d <= k -> k < d + fuel -> k * k <= n -> n mod k <> 0.
Proof.
  induction fuel; intros d n Hc k Hdk Hkf Hsq.
  - lia.
  - simpl in Hc.
    destruct (d * d >? n) eqn:Hstop.
    + apply Nat.leb_le in Hstop.
      assert (d * d <= k * k). { apply Nat.mul_le_mono; assumption. }
      lia.
    + destruct (n mod d =? 0) eqn:Hdiv.
      * discriminate.
      * apply Nat.eqb_neq in Hdiv.
        destruct (Nat.eq_dec k d).
        -- subst. assumption.
        -- apply IHfuel with (d := S d); try assumption.
           lia. lia.
Qed.

Lemma no_divisors_implies_prime : forall n,
  n > 1 ->
  (forall d, 2 <= d -> d * d <= n -> n mod d <> 0) ->
  is_prime n.
Proof.
  intros n Hn Hcheck.
  split; [assumption|].
  intros d Hd.
  destruct (Nat.eq_dec d 1); [left; assumption|].
  destruct (Nat.eq_dec d n); [right; assumption|].
  assert (Hdn: d <> 0). { intro. subst. destruct Hd. rewrite Nat.mul_0_r in H. discriminate. }
  assert (Hd_le_n: d <= n). { apply Nat.divide_pos_le; assumption. }
  assert (Hd_ge_2: d >= 2). { destruct d; try lia. destruct d; try lia. }
  
  destruct (le_lt_dec (d * d) n).
  - assert (Hmod: n mod d = 0). { apply Nat.mod_divide; assumption. }
    exfalso. apply (Hcheck d); assumption.
  - destruct Hd as [q Hq].
    assert (Hq_nz: q <> 0). { intro. subst. rewrite Nat.mul_0_r in Hq. lia. }
    assert (Hq_d: q * d = n) by (rewrite Nat.mul_comm; assumption).
    assert (Hq_le_d: q < d).
    {
      destruct (le_lt_dec d q); try assumption.
      assert (d * d <= q * d). { apply Nat.mul_le_mono_r. assumption. }
      rewrite Hq_d in H. lia.
    }
    assert (Hq_ge_2: q >= 2).
    {
       destruct q; try lia. destruct q; try lia.
       rewrite Nat.mul_1_l in Hq_d. subst. lia.
    }
    assert (Hq_sq: q * q <= n).
    {
       apply Nat.le_trans with (m := q * d).
       apply Nat.mul_le_mono_l. lia.
       rewrite Hq_d. apply le_n.
    }
    assert (Hmod: n mod q = 0). { apply Nat.mod_divide; [assumption|]. exists d. rewrite Nat.mul_comm. assumption. }
    exfalso.
    apply (Hcheck q); try assumption.
Qed.

Definition check_prime (n : nat) : bool :=
  if n <=? 1 then false
  else check_range 2 n n.

Lemma check_prime_correct : forall n, check_prime n = true -> is_prime n.
Proof.
  intros n H.
  unfold check_prime in H.
  destruct (n <=? 1) eqn:Hn.
  - discriminate.
  - apply Nat.leb_nle in Hn.
    apply no_divisors_implies_prime.
    + lia.
    + apply check_range_sound with (fuel := n).
      assumption.
      intros k H2k Hksq.
      assert (k < 2 + n) by lia.
      assumption.
Qed.

Example test_factorize_large : factorize_spec 43121192838 [2; 3; 7186865473].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat constructor; try (apply check_prime_correct; vm_compute; reflexivity).
    + repeat constructor; lia.
Qed.