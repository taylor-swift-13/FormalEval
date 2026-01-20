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

Example test_factorize_185193 : factorize_spec 185193 [3; 3; 3; 19; 19; 19].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + repeat constructor;
      unfold is_prime; split; try lia;
      intros d [k Hk];
      do 20 (destruct d as [|d]; [ try (left; reflexivity); try (right; reflexivity); try lia | ]);
      lia.
    + repeat constructor; lia.
Qed.