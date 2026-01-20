The full content of the Coq output file for the new test case:

```coq
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
  match goal with
  | [ |- is_prime ?p ] =>
    unfold is_prime; split; [ lia | ];
    intros d Hdiv;
    apply Nat.divide_pos_le in Hdiv; [|lia];
    repeat (
      destruct d as [|d];
      [ (* d = 0 *)
        destruct Hdiv as [z Hz]; lia
      | (* d = S ... *)
        try (left; reflexivity);
        try (right; reflexivity);
        try (
           let Hmod := fresh "Hmod" in
           assert (Hmod: p mod (S d) = 0);
           [ apply Nat.divide_div_mul_exact; [lia | apply Hdiv]
           | native_compute in Hmod;
             match goal with
             | [ H : 0 = 0 |- _ ] => fail 1
             | _ => discriminate
             end
           ]
        );
        try lia
      ]
    )
  end.

Example test_factorize_20577 : factorize_spec 20577 [3; 19; 19; 19].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor; solve_prime_const.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.