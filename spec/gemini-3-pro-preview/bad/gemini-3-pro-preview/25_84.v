Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Fixpoint check_range (d p : nat) : bool :=
  match d with
  | 0 | 1 => true
  | S d' => if Nat.eqb (Nat.modulo p (S d')) 0 then false else check_range d' p
  end.

Definition check_prime (p : nat) : bool :=
  if Nat.leb p 1 then false else check_range (pred p) p.

Lemma check_range_correct : forall d p,
  check_range d p = true ->
  forall k, 1 < k <= d -> ~ Nat.divide k p.
Proof.
  induction d.
  - intros p H k Hrange. lia.
  - intros p H k Hrange.
    simpl in H.
    destruct d.
    + lia.
    + destruct (Nat.eqb (Nat.modulo p (S (S d))) 0) eqn:Hmod.
      * discriminate.
      * apply Nat.eqb_neq in Hmod.
        destruct (Nat.eq_dec k (S (S d))).
        -- subst. intro Hdiv.
           apply Nat.mod_divide in Hdiv; try lia.
           contradiction.
        -- apply IHd; auto.
           lia.
Qed.

Lemma check_prime_correct : forall p,
  check_prime p = true -> is_prime p.
Proof.
  intros p H.
  unfold check_prime in H.
  destruct (Nat.leb p 1) eqn:Hle.
  - discriminate.
  - apply Nat.leb_gt in Hle.
    split; [assumption|].
    intros d Hdiv.
    destruct (Nat.eq_dec d 1); [left; auto|].
    destruct (Nat.eq_dec d p); [right; auto|].
    assert (1 < d <= pred p).
    {
      split.
      - destruct d; try lia. destruct d; try lia. assumption.
      - apply Nat.divide_pos_le in Hdiv; try lia.
        assert (d < p) by lia.
        lia.
    }
    apply check_range_correct with (k:=d) in H; try assumption.
    contradiction.
Qed.

Example test_factorize_large : factorize_spec (Z.to_nat 1003001003%Z) [17; 59; 101; 9901].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat constructor.
      * apply check_prime_correct. vm_compute. reflexivity.
      * apply check_prime_correct. vm_compute. reflexivity.
      * apply check_prime_correct. vm_compute. reflexivity.
      * apply check_prime_correct. vm_compute. reflexivity.
    + repeat (constructor; try lia).
Qed.