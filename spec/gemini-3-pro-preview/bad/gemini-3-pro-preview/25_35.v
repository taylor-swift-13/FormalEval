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

Fixpoint no_divisors_below (k : nat) (n : nat) : bool :=
  match k with
  | 0 => true
  | 1 => true
  | S k' => (negb (n mod (S k') =? 0)) && no_divisors_below k' n
  end.

Lemma no_divisors_below_correct : forall k n,
  no_divisors_below k n = true ->
  forall d, 1 < d <= k -> ~ Nat.divide d n.
Proof.
  induction k as [| [| k'] IHk]; intros n Hcheck d Hrange Hdiv.
  - lia.
  - lia.
  - simpl in Hcheck.
    apply andb_true_iff in Hcheck. destruct Hcheck as [Hnd Hrec].
    destruct (Nat.eq_dec d (S (S k'))).
    + subst.
      apply negb_true_iff in Hnd.
      apply Nat.eqb_neq in Hnd.
      destruct Hdiv as [q Hq].
      rewrite Hq in Hnd.
      rewrite Nat.mod_mul in Hnd; try lia.
      congruence.
    + apply IHk; auto. lia.
Qed.

Lemma is_prime_check : forall n,
  1 < n ->
  no_divisors_below (pred n) n = true ->
  is_prime n.
Proof.
  intros n Hgt Hcheck.
  split; auto.
  intros d Hdiv.
  destruct (le_lt_dec d 1) as [Hle|Hlt].
  - assert (d=0 \/ d=1) by lia. destruct H; subst.
    + destruct Hdiv. rewrite Nat.mul_0_r in H. subst. lia.
    + left. reflexivity.
  - destruct (Nat.eq_dec d n).
    + right. auto.
    + assert (d <= pred n).
      { apply Nat.divide_pos_le in Hdiv; try lia. lia. }
      exfalso.
      eapply no_divisors_below_correct; eauto.
Qed.

Example test_factorize_987654320 : factorize_spec 987654320 [2; 2; 2; 2; 5; 37; 333667].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + repeat constructor.
      all: apply is_prime_check; try lia; vm_compute; reflexivity.
    + repeat constructor; lia.
Qed.