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

(* Helper definitions for proving primality by computation *)
Fixpoint check_divisors (d n : nat) {struct d} : bool :=
  match d with
  | 0 => true
  | 1 => true
  | S d' => if (n mod (S d') =? 0) then false else check_divisors d' n
  end.

Lemma check_divisors_correct : forall d n, 
  check_divisors d n = true -> 
  forall k, 1 < k <= d -> ~ Nat.divide k n.
Proof.
  induction d; intros n Hcheck k Hk.
  - lia.
  - destruct d.
    + lia.
    + simpl in Hcheck.
      destruct (n mod S (S d) =? 0) eqn:Hrem.
      * discriminate.
      * apply Nat.eqb_neq in Hrem.
        assert (k = S (S d) \/ k <= S d) as [Hk1 | Hk2] by lia.
        -- subst. intros Hdiv. apply Nat.mod_divide in Hdiv; try lia. contradiction.
        -- apply IHd; auto.
Qed.

Lemma prime_check_sound : forall n, 
  n > 1 -> 
  check_divisors (pred n) n = true -> 
  is_prime n.
Proof.
  intros n Hgt Hcheck.
  split; auto.
  intros d Hdiv.
  destruct (le_lt_dec d 1) as [Hle|Hgt1].
  - destruct d; try lia. left. reflexivity.
  - destruct (le_lt_dec d (pred n)).
    + (* 1 < d <= n-1 *)
      apply check_divisors_correct with (k:=d) in Hcheck; auto.
      contradiction.
    + (* d > n-1 -> d >= n *)
      apply Nat.divide_pos_le in Hdiv; try lia.
      right. lia.
Qed.

Example test_factorize_999985 : factorize_spec 999985 [5; 7; 28571].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    vm_compute. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor.
      * (* is_prime 5 *)
        apply prime_check_sound; try lia.
        vm_compute. reflexivity.
      * (* is_prime 7 *)
        apply prime_check_sound; try lia.
        vm_compute. reflexivity.
      * (* is_prime 28571 *)
        apply prime_check_sound; try lia.
        vm_compute. reflexivity.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.