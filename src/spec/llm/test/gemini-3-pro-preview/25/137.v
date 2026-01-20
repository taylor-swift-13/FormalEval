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

Example test_factorize_50 : factorize_spec 50 [2; 5; 5].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 2 *)
        unfold is_prime. split.
        -- lia.
        -- intros d H.
           destruct d as [| [| [| d'] ]].
           ++ (* d = 0 *)
              destruct H as [z Hz].
              rewrite Nat.mul_0_r in Hz.
              discriminate.
           ++ (* d = 1 *)
              left. reflexivity.
           ++ (* d = 2 *)
              right. reflexivity.
           ++ (* d >= 3 *)
              apply Nat.divide_pos_le in H; try lia.
      * constructor.
        -- (* is_prime 5 *)
           unfold is_prime. split.
           ++ lia.
           ++ intros d H.
              destruct d as [| [| [| [| [| [| d'] ] ] ] ] ].
              ** (* d = 0 *)
                 destruct H as [z Hz].
                 rewrite Nat.mul_0_r in Hz.
                 discriminate.
              ** (* d = 1 *)
                 left. reflexivity.
              ** (* d = 2 *)
                 exfalso. destruct H as [k Hk].
                 destruct k as [| [| [| k'] ] ]; simpl in Hk; try discriminate; lia.
              ** (* d = 3 *)
                 exfalso. destruct H as [k Hk].
                 destruct k as [| [| k'] ]; simpl in Hk; try discriminate; lia.
              ** (* d = 4 *)
                 exfalso. destruct H as [k Hk].
                 destruct k as [| [| k'] ]; simpl in Hk; try discriminate; lia.
              ** (* d = 5 *)
                 right. reflexivity.
              ** (* d >= 6 *)
                 apply Nat.divide_pos_le in H; try lia.
        -- constructor.
           ++ (* is_prime 5 *)
              unfold is_prime. split.
              ** lia.
              ** intros d H.
                 destruct d as [| [| [| [| [| [| d'] ] ] ] ] ].
                 --- (* d = 0 *)
                     destruct H as [z Hz].
                     rewrite Nat.mul_0_r in Hz.
                     discriminate.
                 --- (* d = 1 *)
                     left. reflexivity.
                 --- (* d = 2 *)
                     exfalso. destruct H as [k Hk].
                     destruct k as [| [| [| k'] ] ]; simpl in Hk; try discriminate; lia.
                 --- (* d = 3 *)
                     exfalso. destruct H as [k Hk].
                     destruct k as [| [| k'] ]; simpl in Hk; try discriminate; lia.
                 --- (* d = 4 *)
                     exfalso. destruct H as [k Hk].
                     destruct k as [| [| k'] ]; simpl in Hk; try discriminate; lia.
                 --- (* d = 5 *)
                     right. reflexivity.
                 --- (* d >= 6 *)
                     apply Nat.divide_pos_le in H; try lia.
           ++ constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; simpl; try lia.
Qed.