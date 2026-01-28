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

(* Efficient Primality Checking Helpers *)

Fixpoint check_range (n start len : nat) : bool :=
  match len with
  | 0 => true
  | S len' => 
    if (n mod start =? 0) then false
    else check_range n (S start) len'
  end.

Lemma check_range_correct : forall n start len,
  start <> 0 ->
  check_range n start len = true ->
  forall d, start <= d < start + len -> ~ Nat.divide d n.
Proof.
  induction len; simpl; intros Hstart Hcheck d Hrange.
  - lia.
  - destruct (n mod start =? 0) eqn:Heq.
    + discriminate.
    + apply Nat.eqb_neq in Heq.
      assert (Hnodiv: ~ Nat.divide start n).
      { intros Hdiv. apply Nat.mod_divide in Hdiv; auto. congruence. }
      destruct (Nat.eq_dec d start).
      * subst. assumption.
      * apply IHlen; auto.
        -- lia.
        -- lia.
Qed.

Lemma is_prime_check : forall n,
  1 < n ->
  check_range n 2 (n - 2) = true ->
  is_prime n.
Proof.
  intros n Hgt Hcheck.
  split; auto.
  intros d Hdiv.
  destruct (le_lt_dec d 1).
  - destruct d; try lia. left. auto.
  - destruct (Nat.eq_dec d n).
    + right. auto.
    + assert (d_in_range: 2 <= d < 2 + (n - 2)).
      { split. lia.
        apply Nat.le_lt_trans with (m:=n); auto.
        apply Nat.divide_pos_le in Hdiv.
        * destruct (Nat.eq_dec d n); try congruence.
          lia.
        * lia.
      }
      apply check_range_correct with (d := d) in Hcheck; auto; try lia.
      contradiction.
Qed.

Example test_factorize_large : factorize_spec (Z.to_nat 123456790%Z) [2; 5; 37; 333667].
Proof.
  unfold factorize_spec.
  split.
  - (* Product check *)
    vm_compute. reflexivity.
  - split.
    + (* Primality check *)
      repeat constructor.
      * apply is_prime_check; try lia. vm_compute. reflexivity.
      * apply is_prime_check; try lia. vm_compute. reflexivity.
      * apply is_prime_check; try lia. vm_compute. reflexivity.
      * apply is_prime_check; try lia. vm_compute. reflexivity.
    + (* Sorted check *)
      repeat constructor; simpl; try lia.
Qed.