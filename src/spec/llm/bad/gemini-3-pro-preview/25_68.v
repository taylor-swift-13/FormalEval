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

Example test_factorize_76 : factorize_spec 76 [2; 2; 19].
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
      * (* is_prime 19 *)
        unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [|d]. { destruct Hdiv as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate. }
           destruct d as [|d]. { left. reflexivity. }
           (* d >= 2 *)
           apply Nat.divide_pos_le in Hdiv as Hle; [| lia].
           do 17 (destruct d as [|d]; [
             exfalso; apply Nat.mod_divide in Hdiv; [| lia]; simpl in Hdiv; discriminate
           | ]).
           destruct d as [|d]. { right. reflexivity. }
           lia.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.