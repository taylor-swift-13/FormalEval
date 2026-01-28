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

Example test_factorize_52 : factorize_spec 52 [2; 2; 13].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      assert (H_prime_2 : is_prime 2).
      {
        unfold is_prime. split.
        - lia.
        - intros d Hdiv.
          destruct d as [| [| [| d'] ]].
          + destruct Hdiv as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate.
          + left. reflexivity.
          + right. reflexivity.
          + apply Nat.divide_pos_le in Hdiv; try lia.
      }
      assert (H_prime_13 : is_prime 13).
      {
        unfold is_prime. split.
        - lia.
        - intros d Hdiv.
          destruct d as [|d]. { destruct Hdiv as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate. }
          destruct d as [|d]. { left. reflexivity. }
          apply Nat.mod_divide in Hdiv; [| lia].
          destruct d as [|d]; [simpl in Hdiv; discriminate|]. (* 2 *)
          destruct d as [|d]; [simpl in Hdiv; discriminate|]. (* 3 *)
          destruct d as [|d]; [simpl in Hdiv; discriminate|]. (* 4 *)
          destruct d as [|d]; [simpl in Hdiv; discriminate|]. (* 5 *)
          destruct d as [|d]; [simpl in Hdiv; discriminate|]. (* 6 *)
          destruct d as [|d]; [simpl in Hdiv; discriminate|]. (* 7 *)
          destruct d as [|d]; [simpl in Hdiv; discriminate|]. (* 8 *)
          destruct d as [|d]; [simpl in Hdiv; discriminate|]. (* 9 *)
          destruct d as [|d]; [simpl in Hdiv; discriminate|]. (* 10 *)
          destruct d as [|d]; [simpl in Hdiv; discriminate|]. (* 11 *)
          destruct d as [|d]; [simpl in Hdiv; discriminate|]. (* 12 *)
          destruct d as [|d]; [right; reflexivity|]. (* 13 *)
          simpl in Hdiv. discriminate.
      }
      repeat constructor; assumption.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.