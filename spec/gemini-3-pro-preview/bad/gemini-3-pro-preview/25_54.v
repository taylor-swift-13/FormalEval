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

Example test_factorize_56 : factorize_spec 56 [2; 2; 2; 7].
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
           destruct d as [| [| [| d'] ]].
           ++ destruct Hdiv as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate.
           ++ left. reflexivity.
           ++ right. reflexivity.
           ++ apply Nat.divide_pos_le in Hdiv; try lia.
      * (* is_prime 2 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [| [| [| d'] ]].
           ++ destruct Hdiv as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate.
           ++ left. reflexivity.
           ++ right. reflexivity.
           ++ apply Nat.divide_pos_le in Hdiv; try lia.
      * (* is_prime 2 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [| [| [| d'] ]].
           ++ destruct Hdiv as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate.
           ++ left. reflexivity.
           ++ right. reflexivity.
           ++ apply Nat.divide_pos_le in Hdiv; try lia.
      * (* is_prime 7 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [| [| [| [| [| [| [| [| d']]]]]]]]].
           ++ (* d = 0 *) destruct Hdiv as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate.
           ++ (* d = 1 *) left. reflexivity.
           ++ (* d = 2 *) exfalso. destruct Hdiv as [k Hk]. destruct k as [|[|[|[|]]]]; simpl in Hk; try lia.
           ++ (* d = 3 *) exfalso. destruct Hdiv as [k Hk]. destruct k as [|[|[|]]]; simpl in Hk; try lia.
           ++ (* d = 4 *) exfalso. destruct Hdiv as [k Hk]. destruct k as [|[|]]; simpl in Hk; try lia.
           ++ (* d = 5 *) exfalso. destruct Hdiv as [k Hk]. destruct k as [|[|]]; simpl in Hk; try lia.
           ++ (* d = 6 *) exfalso. destruct Hdiv as [k Hk]. destruct k as [|[|]]; simpl in Hk; try lia.
           ++ (* d = 7 *) right. reflexivity.
           ++ (* d >= 8 *) apply Nat.divide_pos_le in Hdiv; try lia.
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.