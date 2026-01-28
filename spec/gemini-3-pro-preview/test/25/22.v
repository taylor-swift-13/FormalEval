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

Example test_factorize_29 : factorize_spec 29 [29].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 29 *)
        unfold is_prime. split.
        -- (* 29 > 1 *)
           lia.
        -- (* Divisors check *)
           intros d Hdiv.
           (* d = 0 *)
           destruct d as [|d]. {
             destruct Hdiv as [z Hz].
             rewrite Nat.mul_0_r in Hz.
             discriminate.
           }
           (* d = 1 *)
           destruct d as [|d]. {
             left. reflexivity.
           }
           (* Check d = 2 to 28 *)
           do 27 (
             destruct d as [|d]; [
               apply Nat.mod_divide in Hdiv; [|lia];
               simpl in Hdiv; discriminate
             | ]
           ).
           (* d = 29 *)
           destruct d as [|d]. {
             right. reflexivity.
           }
           (* d > 29 *)
           apply Nat.divide_pos_le in Hdiv; try lia.
      * (* End of list *)
        constructor.
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.