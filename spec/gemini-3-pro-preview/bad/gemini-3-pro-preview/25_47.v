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

Example test_factorize_999983 : factorize_spec 999983 [999983].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor.
      * (* is_prime 999983 *)
        unfold is_prime. split.
        -- (* 999983 > 1 *)
           lia.
        -- (* Divisors check *)
           intros d Hdiv.
           (* Use Z.prime for efficient checking *)
           assert (Hz: Z.prime 999983%Z).
           { destruct (Z.prime_dec 999983%Z) as [H|H].
             - exact H.
             - vm_compute in H. discriminate. }
           (* Bridge to Nat.prime *)
           assert (Hn: Nat.prime 999983).
           { apply prime_of_Z_fact.
             replace (Z.of_nat 999983) with 999983%Z by (vm_compute; reflexivity).
             exact Hz. }
           unfold Nat.prime in Hn.
           destruct Hn as [_ Hforall].
           apply Hforall.
           exact Hdiv.
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.