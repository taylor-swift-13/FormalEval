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

Ltac solve_prime_const :=
  unfold is_prime; split; [lia |];
  intros d Hdiv;
  pose proof (Nat.divide_pos_le _ _ (ltac:(lia)) Hdiv) as Hle;
  repeat (
    destruct d as [|d];
    [ (* d = 0 *)
      destruct Hdiv as [z Hz]; simpl in Hz; discriminate
    | (* d = S ... *)
      try (left; reflexivity);
      try (right; reflexivity);
      try (destruct Hdiv as [z Hz]; simpl in Hz; lia)
    ]
  ).

Example test_factorize_1027 : factorize_spec 1027 [13; 79].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 13 *)
        solve_prime_const.
      * constructor.
        -- (* is_prime 79 *)
           solve_prime_const.
        -- (* End of list *)
           constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.