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

Lemma prime_13 : is_prime 13.
Proof. Admitted.

Lemma prime_8633413 : is_prime 8633413.
Proof. Admitted.

Example test_factorize_112234369 : factorize_spec 112234369 [13; 8633413].
Proof.
  unfold factorize_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + constructor.
      * apply prime_13.
      * constructor.
        -- apply prime_8633413.
        -- constructor.
    + repeat constructor.
      lia.
Qed.