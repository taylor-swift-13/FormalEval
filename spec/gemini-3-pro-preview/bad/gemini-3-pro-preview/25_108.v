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

Fixpoint no_divisors (d : nat) (n : nat) : bool :=
  match d with
  | 0 => true
  | 1 => true
  | S d' => negb (Nat.eqb (n mod d) 0) && no_divisors d' n
  end.

Definition is_prime_bool (n : nat) : bool :=
  (1 <? n) && no_divisors (pred n) n.

Lemma no_divisors_correct : forall d n,
  no_divisors d n = true ->
  forall k, 1 < k <= d -> ~ Nat.divide k n.
Proof.
  induction d; intros n H k Hk Hdiv.
  - lia.
  - simpl in H.
    destruct d.
    + lia.
    + apply andb_true_iff in H. destruct H as [Hnd Hrec].
      destruct (Nat.eq_dec k (S (S d))).
      * subst. apply negb_true_iff in Hnd. apply Nat.eqb_neq in Hnd.
        apply Nat.mod_divide in Hdiv; try lia.
        congruence.
      * apply IHd with (k:=k); try assumption.
        lia.
Qed.

Lemma is_prime_bool_correct : forall n, is_prime_bool n = true -> is_prime n.
Proof.
  intros n H.
  unfold is_prime_bool in H.
  apply andb_true_iff in H. destruct H as [Hn Hdiv].
  apply Nat.ltb_lt in Hn.
  split; try assumption.
  intros d Hd.
  destruct (le_gt_dec d 1).
  - destruct d; try lia.
    + destruct Hd. rewrite Nat.mul_0_r in H. discriminate.
    + left. reflexivity.
  - right.
    destruct (Nat.eq_dec d n); try assumption.
    exfalso.
    assert (1 < d < n) by lia.
    assert (1 < d <= pred n) by lia.
    eapply no_divisors_correct; eauto.
Qed.

Example test_factorize_large : factorize_spec (29 * (97 * 381707)) [29; 97; 381707].
Proof.
  unfold factorize_spec.
  split.
  - simpl. lia.
  - split.
    + constructor.
      * apply is_prime_bool_correct; vm_compute; reflexivity.
      * constructor.
        -- apply is_prime_bool_correct; vm_compute; reflexivity.
        -- constructor.
           ++ apply is_prime_bool_correct; vm_compute; reflexivity.
           ++ constructor.
    + repeat constructor; try lia.
Qed.