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

Fixpoint check_range (n d count : nat) : bool :=
  match count with
  | 0 => true
  | S c => if (n mod d) =? 0 then false else check_range n (S d) c
  end.

Definition check_prime (n : nat) : bool :=
  if n <=? 1 then false
  else check_range n 2 (n - 2).

Lemma check_range_correct : forall n d c,
  d > 0 ->
  check_range n d c = true ->
  forall x, d <= x < d + c -> ~ Nat.divide x n.
Proof.
  induction c; intros Hd Hcheck x Hrange.
  - lia.
  - simpl in Hcheck.
    destruct (n mod d =? 0) eqn:Hmod.
    + discriminate.
    + apply Nat.eqb_neq in Hmod.
      destruct Hrange as [Hge Hlt].
      assert (x = d \/ d < x) by lia.
      destruct H as [Heq | Hgt].
      * subst x. intros Hdiv.
        apply Nat.mod_divide in Hdiv; auto.
      * apply IHc; try lia.
        -- assumption.
        -- split; lia.
Qed.

Lemma check_prime_correct : forall n, check_prime n = true -> is_prime n.
Proof.
  intros n H.
  unfold check_prime in H.
  destruct (n <=? 1) eqn:Hle.
  - discriminate.
  - apply Nat.leb_gt in Hle.
    unfold is_prime. split; auto.
    intros d Hdiv.
    destruct (le_lt_dec d 1).
    + destruct d; try lia. left. auto.
    + destruct (Nat.eq_dec d n).
      * right. auto.
      * apply Nat.divide_pos_le in Hdiv; try lia.
        assert (2 <= d < 2 + (n - 2)) by lia.
        apply check_range_correct with (x:=d) in H; try lia.
        contradiction.
Qed.

Example test_factorize_999979 : factorize_spec 999979 [999979].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * apply check_prime_correct.
        vm_compute. reflexivity.
      * constructor.
    + repeat constructor.
Qed.