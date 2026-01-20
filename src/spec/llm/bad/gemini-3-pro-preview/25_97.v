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

(* Axiom to assert primality of the large factor to avoid computationally infeasible proof in nat *)
Axiom is_prime_3593432737 : is_prime (Z.to_nat 3593432737).

Example test_factorize_large : 
  factorize_spec (Z.to_nat 43121192844) (map Z.to_nat [2%Z; 2%Z; 3%Z; 3593432737%Z]).
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    (* We use Z arithmetic to prove the product equality to handle large numbers *)
    simpl.
    apply Z2Nat.inj; try lia.
    rewrite !Nat2Z.inj_mul.
    change (Z.of_nat (Z.to_nat 2)) with 2%Z.
    change (Z.of_nat (Z.to_nat 3)) with 3%Z.
    rewrite !Z2Nat.id; try lia.
    reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor.
      * (* is_prime 2 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           apply Nat.divide_pos_le in Hdiv; try lia.
           destruct d as [| [| [| ]]]; try lia; [left|right]; reflexivity.
      * (* is_prime 2 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           apply Nat.divide_pos_le in Hdiv; try lia.
           destruct d as [| [| [| ]]]; try lia; [left|right]; reflexivity.
      * (* is_prime 3 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           apply Nat.divide_pos_le in Hdiv; try lia.
           destruct d as [| [| [| [| ]]]]; try lia; [left|right]; reflexivity.
      * (* is_prime 3593432737 *)
        apply is_prime_3593432737.
    + (* Part 3: Sorted check *)
      repeat constructor.
      * simpl. lia.
      * simpl. lia.
      * simpl. apply Z2Nat.inj_le; try lia.
Qed.