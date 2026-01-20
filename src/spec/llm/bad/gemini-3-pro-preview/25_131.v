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

Definition check_no_divisors (p : nat) : bool :=
  forallb (fun d => negb (p mod d =? 0)) (seq 2 (p - 2)).

Lemma check_no_divisors_correct : forall p,
  p > 1 ->
  check_no_divisors p = true ->
  is_prime p.
Proof.
  intros p Hgt Hcheck.
  split; auto.
  intros d Hdiv.
  destruct (le_lt_dec d 1) as [Hle1 | Hgt1].
  - destruct d.
    + destruct Hdiv as [k Hk]. rewrite Nat.mul_0_r in Hk. discriminate.
    + left. reflexivity.
  - destruct (le_lt_dec p d) as [Hlep | Hltp].
    + apply Nat.divide_pos_le in Hdiv; try lia.
      right. lia.
    + exfalso.
      unfold check_no_divisors in Hcheck.
      rewrite forallb_forall in Hcheck.
      assert (In d (seq 2 (p - 2))) as Hin.
      { apply in_seq. lia. }
      apply Forall_forall with (x := d) in Hcheck; auto.
      apply Nat.mod_divide in Hdiv; try lia.
      rewrite Hdiv in Hcheck.
      simpl in Hcheck.
      discriminate.
Qed.

Example test_factorize_987654325 : factorize_spec 987654325 [5; 5; 7; 337; 16747].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + repeat (apply Forall_cons; [ apply check_no_divisors_correct; [lia | vm_compute; reflexivity] | ]).
      apply Forall_nil.
    + repeat constructor; lia.
Qed.