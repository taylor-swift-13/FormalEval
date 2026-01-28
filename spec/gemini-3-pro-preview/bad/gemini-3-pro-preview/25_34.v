Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Example test_factorize_1022 : factorize_spec 1022 [2; 7; 73].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor.
      * (* is_prime 2 *)
        unfold is_prime. split. lia.
        intros d [k Hk]. nia.
      * (* is_prime 7 *)
        unfold is_prime. split. lia.
        intros d [k Hk]. nia.
      * (* is_prime 73 *)
        unfold is_prime. split. lia.
        intros d [k Hk]. nia.
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.