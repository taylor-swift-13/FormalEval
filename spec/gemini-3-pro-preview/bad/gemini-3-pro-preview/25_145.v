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

Example test_factorize_42 : factorize_spec 42 [2; 3; 7].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      repeat constructor.
      * (* is_prime 2 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [| [| [| ]]]; try lia.
           ++ destruct Hdiv as [k Hk]. rewrite Nat.mul_0_r in Hk. discriminate.
           ++ left. reflexivity.
           ++ right. reflexivity.
           ++ apply Nat.divide_pos_le in Hdiv; lia.
      * (* is_prime 3 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [| [| [| [| ]]]]; try lia.
           ++ destruct Hdiv as [k Hk]. rewrite Nat.mul_0_r in Hk. discriminate.
           ++ left. reflexivity.
           ++ exfalso. destruct Hdiv as [k Hk]. destruct k as [| [| ]]; simpl in Hk; lia.
           ++ right. reflexivity.
           ++ apply Nat.divide_pos_le in Hdiv; lia.
      * (* is_prime 7 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [| [| [| [| [| [| [| [| ]]]]]]]]; try lia.
           ++ destruct Hdiv as [k Hk]. rewrite Nat.mul_0_r in Hk. discriminate.
           ++ left. reflexivity.
           ++ exfalso. destruct Hdiv as [k Hk]. destruct k as [| [| [| [| ]]]]; simpl in Hk; lia.
           ++ exfalso. destruct Hdiv as [k Hk]. destruct k as [| [| [| ]]]; simpl in Hk; lia.
           ++ exfalso. destruct Hdiv as [k Hk]. destruct k as [| [| ]]; simpl in Hk; lia.
           ++ exfalso. destruct Hdiv as [k Hk]. destruct k as [| [| ]]; simpl in Hk; lia.
           ++ exfalso. destruct Hdiv as [k Hk]. destruct k as [| [| ]]; simpl in Hk; lia.
           ++ right. reflexivity.
           ++ apply Nat.divide_pos_le in Hdiv; lia.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.