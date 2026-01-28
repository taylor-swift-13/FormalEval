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

Ltac prove_prime_force :=
  unfold is_prime; split; [lia|];
  intros d Hdiv;
  apply Nat.divide_pos_le in Hdiv; [|lia];
  do 20 (destruct d as [|d]; [
    try (left; reflexivity);    (* d = 1 *)
    try (right; reflexivity);   (* d = p *)
    try (exfalso; destruct Hdiv as [k Hk]; lia); (* 1 < d < p or does not divide *)
    try lia                     (* d = 0 *)
  |]);
  lia. (* d > 20 *)

Example test_factorize_3249 : factorize_spec 3249 [3; 3; 19; 19].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * prove_prime_force.
      * constructor.
        -- prove_prime_force.
        -- constructor.
           ++ prove_prime_force.
           ++ constructor.
              ** prove_prime_force.
              ** constructor.
    + repeat constructor; lia.
Qed.