Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Lemma prime_Z_of_nat (n : nat) : prime (Z.of_nat n) -> is_prime n.
Proof.
  intros Hp.
  split.
  - apply Z2Nat.inj_lt with (n:=1%Z) (m:=Z.of_nat n); try lia.
    apply Hp.
  - intros d Hd.
    apply Nat2Z.inj_divide in Hd.
    pose proof (prime_divisors (Z.of_nat n) Hp (Z.of_nat d) Hd) as [H1 | [H1 | [H1 | H1]]].
    + left. apply Z2Nat.inj; try lia. exact H1.
    + lia.
    + right. apply Z2Nat.inj; try lia. exact H1.
    + lia.
Qed.

Ltac prove_prime_Z :=
  match goal with
  | |- prime ?n =>
      let x := eval vm_compute in (prime_dec n) in
      match x with
      | left ?p => exact p
      | right _ => fail "Not a prime"
      end
  end.

Example test_factorize_999980 : factorize_spec 999980 [2; 2; 5; 49999].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor; [ apply prime_Z_of_nat; prove_prime_Z | ].
      constructor; [ apply prime_Z_of_nat; prove_prime_Z | ].
      constructor; [ apply prime_Z_of_nat; prove_prime_Z | ].
      constructor; [ apply prime_Z_of_nat; prove_prime_Z | ].
      constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.