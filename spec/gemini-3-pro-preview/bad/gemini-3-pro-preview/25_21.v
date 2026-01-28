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

Ltac solve_prime :=
  unfold is_prime; split; [ lia |
    intros d Hdiv;
    apply Nat.divide_pos_le in Hdiv; [| lia];
    do 25 (destruct d; [
      match goal with
      | [ H : Nat.divide 0 _ |- _ ] =>
          destruct H as [? Hz]; rewrite Nat.mul_0_r in Hz; discriminate
      | [ |- 1 = 1 \/ _ ] => left; reflexivity
      | [ |- ?x = 1 \/ ?x = ?p ] =>
          try (right; reflexivity);
          try (exfalso; apply Nat.mod_divide in Hdiv; [ simpl in Hdiv; discriminate | lia ])
      end
    | ]);
    try lia
  ].

Example test_factorize_1026 : factorize_spec 1026 [2; 3; 3; 3; 19].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + repeat (constructor; try solve_prime).
    + repeat constructor.
Qed.