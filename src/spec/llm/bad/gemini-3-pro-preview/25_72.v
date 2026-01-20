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

Lemma is_prime_via_Z : forall n,
  (1 < n)%nat ->
  prime (Z.of_nat n) ->
  is_prime n.
Proof.
  intros n Hlt Hprime.
  split; [lia|].
  intros d Hdiv.
  apply Z.numtheory.prime_divisors in Hprime.
  assert (Zdiv: (Z.of_nat d | Z.of_nat n)%Z).
  { destruct Hdiv as [x Hx]. exists (Z.of_nat x). rewrite <- Nat2Z.inj_mul. congruence. }
  specialize (Hprime (Z.of_nat d) Zdiv).
  destruct Hprime as [H1 | [Hn | [H_1 | H_n]]].
  - left. apply Nat2Z.inj. exact H1.
  - right. apply Nat2Z.inj. exact Hn.
  - exfalso. assert (0 <= Z.of_nat d)%Z by apply Nat2Z.is_nonneg. rewrite H_1 in H. lia.
  - exfalso. assert (0 <= Z.of_nat d)%Z by apply Nat2Z.is_nonneg. 
    assert (0 < Z.of_nat n)%Z by lia.
    rewrite H_n in H. lia.
Qed.

Example test_factorize_large : factorize_spec 112234371 [3; 37411457].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl fold_right. lia.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 3 *)
        apply is_prime_via_Z; [lia|].
        destruct (prime_dec (Z.of_nat 3)) as [H|H]; [exact H|discriminate].
      * constructor.
        -- (* is_prime 37411457 *)
           apply is_prime_via_Z; [lia|].
           (* Use destruct to evaluate the decidable primality check *)
           destruct (prime_dec (Z.of_nat 37411457)) as [H|H]; [exact H|elim H].
        -- constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.