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

Example test_factorize_125 : factorize_spec 125 [5; 5; 5].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_nil ] ] ].
      all: unfold is_prime; split; [ lia | ];
           intros d Hdiv;
           destruct d as [| [| [| [| [| [| ]]]]]]]; try lia.
      * (* d = 0 *)
        destruct Hdiv as [k Hk]; simpl in Hk; discriminate.
      * (* d = 1 *)
        left; reflexivity.
      * (* d = 2 *)
        destruct Hdiv as [k Hk]; destruct k as [| [| [| ]]]; simpl in Hk; try discriminate; lia.
      * (* d = 3 *)
        destruct Hdiv as [k Hk]; destruct k as [| [| ]]]; simpl in Hk; try discriminate; lia.
      * (* d = 4 *)
        destruct Hdiv as [k Hk]; destruct k as [| [| ]]]; simpl in Hk; try discriminate; lia.
      * (* d = 5 *)
        right; reflexivity.
      * (* d >= 6 *)
        apply Nat.divide_pos_le in Hdiv; try lia.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.