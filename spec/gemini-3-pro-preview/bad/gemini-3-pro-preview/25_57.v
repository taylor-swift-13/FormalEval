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

Fixpoint no_divisors_below (d : nat) (n : nat) : bool :=
  match d with
  | 0 => true
  | 1 => true
  | S d' => if n mod d =? 0 then false else no_divisors_below d' n
  end.

Lemma no_divisors_below_correct : forall d n,
  no_divisors_below d n = true ->
  forall k, 1 < k <= d -> ~ Nat.divide k n.
Proof.
  induction d; intros n Hcheck k Hk.
  - lia.
  - simpl in Hcheck.
    destruct d.
    + lia.
    + destruct (n mod S (S d) =? 0) eqn:Hrem.
      * discriminate.
      * apply Nat.eqb_neq in Hrem.
        destruct (Nat.eq_dec k (S (S d))).
        -- subst. intro Hdiv. apply Nat.mod_divide in Hdiv; [|lia]. contradiction.
        -- apply IHd; auto. lia.
Qed.

Lemma prime_check_correct : forall p,
  p > 1 ->
  no_divisors_below (pred p) p = true ->
  is_prime p.
Proof.
  intros p Hp Hcheck.
  split; auto.
  intros d Hdiv.
  destruct (le_gt_dec d 1).
  - assert (d = 0 \/ d = 1) by lia. destruct H as [-> | ->].
    + destruct Hdiv. rewrite Nat.mul_0_r in H. subst p. lia.
    + left. reflexivity.
  - destruct (ge_dec d p).
    + apply Nat.divide_pos_le in Hdiv; [|lia].
      assert (d = p) by lia. right. assumption.
    + exfalso.
      apply (no_divisors_below_correct (pred p) p Hcheck d).
      * lia.
      * assumption.
Qed.

Example test_factorize_1003000999 : factorize_spec 1003000999 [7; 11; 13; 41; 24439].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + repeat constructor.
      * apply prime_check_correct; [lia | vm_compute; reflexivity].
      * apply prime_check_correct; [lia | vm_compute; reflexivity].
      * apply prime_check_correct; [lia | vm_compute; reflexivity].
      * apply prime_check_correct; [lia | vm_compute; reflexivity].
      * apply prime_check_correct; [lia | vm_compute; reflexivity].
    + repeat constructor; lia.
Qed.