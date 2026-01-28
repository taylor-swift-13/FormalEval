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

Fixpoint check_divisors (n d : nat) : bool :=
  match d with
  | 0 => true
  | 1 => true
  | S d' => if (n mod d =? 0) then false else check_divisors n d'
  end.

Definition is_prime_check (n : nat) : bool :=
  if n <=? 1 then false else check_divisors n (pred n).

Lemma check_divisors_correct : forall n d,
  check_divisors n d = true ->
  forall k, 1 < k <= d -> ~ Nat.divide k n.
Proof.
  induction d; intros Hcheck k Hk Hdiv.
  - lia.
  - destruct d.
    + lia.
    + simpl in Hcheck.
      destruct (n mod S (S d) =? 0) eqn:Hrem.
      * discriminate.
      * apply Nat.eqb_neq in Hrem.
        apply IHd in Hcheck.
        -- destruct (Nat.eq_dec k (S (S d))).
           ++ subst. rewrite Nat.mod_divide in Hrem; try lia.
              contradiction.
           ++ apply Hcheck; try lia.
        -- lia.
Qed.

Lemma is_prime_check_correct : forall n,
  is_prime_check n = true -> is_prime n.
Proof.
  intros n H.
  unfold is_prime_check in H.
  destruct (n <=? 1) eqn:Hle.
  - discriminate.
  - apply Nat.leb_gt in Hle.
    split; try lia.
    intros d Hdiv.
    destruct (le_lt_dec d 1) as [Hsmall | Hlarge].
    + destruct d; try lia. left. reflexivity.
    + destruct (Nat.eq_dec d n) as [Heq | Hneq].
      * right. auto.
      * assert (Hrange: 1 < d <= pred n).
        { split; try lia. apply Nat.lt_le_pred.
          apply Nat.divide_pos_le in Hdiv; try lia.
          destruct (Nat.eq_dec d n); try lia. }
        apply check_divisors_correct with (k := d) in H; try lia.
        -- contradiction.
        -- lia.
Qed.

Example test_factorize_7919 : factorize_spec 7919 [7919].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * apply is_prime_check_correct.
        vm_compute. reflexivity.
      * constructor.
    + repeat constructor.
Qed.