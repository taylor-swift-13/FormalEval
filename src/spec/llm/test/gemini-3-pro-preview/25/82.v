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

Example test_factorize_67 : factorize_spec 67 [67].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 67 *)
        unfold is_prime. split.
        -- (* 67 > 1 *)
           lia.
        -- (* Divisors check *)
           intros d Hdiv.
           assert (Hle : d <= 67). { apply Nat.divide_pos_le in Hdiv; lia. }
           do 67 (destruct d as [|d]; 
                  [ try (left; reflexivity); 
                    try (destruct Hdiv as [k Hk]; simpl in Hk; lia)
                  | apply le_S_n in Hle ]).
           destruct d as [|d].
           ++ right. reflexivity.
           ++ lia.
      * (* End of list *)
        constructor.
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.