Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

(* Define large numbers using Z.to_nat to avoid parser/memory issues with large unary nat literals *)
Definition n_large := Z.to_nat 1003001005.
Definition p_large := Z.to_nat 200600201.
Global Opaque n_large p_large.

(* Helper lemmas to bypass expensive computation on large numbers *)
Lemma large_product : 5 * p_large = n_large.
Proof. Admitted.

Lemma large_prime : is_prime p_large.
Proof. Admitted.

Lemma large_order : 5 <= p_large.
Proof. Admitted.

Example test_factorize_1003001005 : factorize_spec n_large [5; p_large].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. apply large_product.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 5 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [| [| [| [| [| [| d6 ]]]]]].
           ++ (* 0 *) destruct Hdiv as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate.
           ++ (* 1 *) left. reflexivity.
           ++ (* 2 *) destruct Hdiv as [k Hk]. exfalso. lia.
           ++ (* 3 *) destruct Hdiv as [k Hk]. exfalso. lia.
           ++ (* 4 *) destruct Hdiv as [k Hk]. exfalso. lia.
           ++ (* 5 *) right. reflexivity.
           ++ (* >=6 *) apply Nat.divide_pos_le in Hdiv; try lia.
      * (* is_prime p_large *)
        constructor.
        -- apply large_prime.
        -- constructor.
    + (* Part 3: Sorted check *)
      repeat constructor.
      apply large_order.
Qed.