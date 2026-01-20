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

Fixpoint check_divs (d max p : nat) : bool :=
  match max with
  | 0 => true
  | S m => 
      if (p mod d) =? 0 then false
      else check_divs (S d) m p
  end.

Lemma check_divs_correct : forall max d p, 
  check_divs d max p = true -> 
  (forall n, d <= n -> n < d + max -> ~ Nat.divide n p).
Proof.
  induction max; intros.
  - lia.
  - simpl in H.
    destruct ((p mod d) =? 0) eqn:Heq.
    + discriminate.
    + apply Nat.eqb_neq in Heq.
      intros n Hdn Hnm.
      assert (n = d \/ S d <= n) by lia.
      destruct H0.
      * subst. intros Hdiv. apply Nat.mod_divide in Hdiv; try lia. congruence.
      * apply IHmax; auto. lia. lia.
Qed.

Definition check_prime (p : nat) :=
  (1 < p) /\ (forall n, 2 <= n -> n * n <= p -> ~ (Nat.divide n p)).

Lemma check_prime_correct : forall p, check_prime p -> is_prime p.
Proof.
  intros p [H1 H2].
  split; auto.
  intros d Hdiv.
  destruct (le_lt_dec d 1).
  { destruct d; try lia. destruct d; try lia. left; auto. }
  destruct (Nat.eq_dec d p); auto.
  right. auto.
  exfalso.
  assert (Hdp: 1 < d < p) by lia.
  destruct Hdiv as [k Hk].
  assert (Hk_pos: k > 0). { destruct k; simpl in Hk; try lia. }
  assert (Hk_bound: 1 < k < p). 
  { split. 
    - destruct k; try lia. destruct k; try lia.
      rewrite <- Hk in Hdp. destruct d; try lia. destruct d; try lia.
      simpl in Hk. lia.
    - rewrite <- (Nat.mul_1_r p). rewrite Hk. 
      rewrite Nat.mul_comm. apply Nat.mul_lt_mono_pos_l; try lia.
  }
  destruct (le_lt_dec (d*d) p).
  - apply (H2 d); auto. exists k; auto.
  - destruct (le_lt_dec (k*k) p).
    + apply (H2 k); auto. 
      * lia.
      * exists d. rewrite Nat.mul_comm. auto.
    + assert (d * k > p).
      { apply Nat.nle_gt in l. apply Nat.nle_gt in l0.
        assert (d * d * (k * k) > p * p). { apply Nat.mul_lt_mono; auto; lia. }
        rewrite Nat.mul_shuffle0 in H. rewrite <- Nat.pow_2_r in H.
        rewrite <- Nat.pow_2_r in H. rewrite <- Nat.pow_2_r in H.
        apply Nat.square_lt_mono_nonneg in H; try lia. }
      rewrite Hk in H. lia.
Qed.

Definition solve_prime (p limit : nat) : Prop :=
  check_divs 2 (limit - 1) p = true /\ limit * limit <= p /\ (S limit) * (S limit) > p.

Lemma solve_prime_correct : forall p limit, 
  p > 1 -> solve_prime p limit -> is_prime p.
Proof.
  intros p limit Hp [Hcheck [Hsq1 Hsq2]].
  apply check_prime_correct.
  split; auto.
  intros n Hn2 Hnsq.
  assert (n <= limit).
  {
    destruct (le_lt_dec n limit); auto.
    assert (n * n > p).
    { apply Nat.le_lt_trans with (m := (S limit) * (S limit)); try lia.
      apply Nat.mul_le_mono; lia. }
    lia.
  }
  eapply check_divs_correct in Hcheck; eauto; try lia.
Qed.

Example test_factorize_43121192841 : factorize_spec (Z.to_nat 43121192841%Z) [3; 3; 131; 1237; 29567].
Proof.
  unfold factorize_spec.
  split.
  - simpl. rewrite ?Nat2Z.inj_mul.
    rewrite Z2Nat.id; [|vm_compute; reflexivity].
    vm_compute. reflexivity.
  - split.
    + repeat constructor.
      * apply (solve_prime_correct _ 1); try lia; split; [vm_compute; reflexivity | split; [lia|lia]].
      * apply (solve_prime_correct _ 1); try lia; split; [vm_compute; reflexivity | split; [lia|lia]].
      * apply (solve_prime_correct _ 11); try lia; split; [vm_compute; reflexivity | split; [lia|lia]].
      * apply (solve_prime_correct _ 35); try lia; split; [vm_compute; reflexivity | split; [lia|lia]].
      * apply (solve_prime_correct _ 171); try lia; split; [vm_compute; reflexivity | split; [lia|lia]].
    + repeat constructor; lia.
Qed.