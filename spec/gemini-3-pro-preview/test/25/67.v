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

Example test_factorize_83 : factorize_spec 83 [83].
Proof.
  unfold factorize_spec.
  split.
  - (* Part 1: Product check *)
    simpl. reflexivity.
  - split.
    + (* Part 2: Primality check *)
      constructor.
      * (* is_prime 83 *)
        unfold is_prime. split.
        -- (* 83 > 1 *)
           lia.
        -- (* Divisors check *)
           intros d [k Hk].
           (* Check bounds: either d is small or k is small. *)
           assert (d <= 9 \/ k <= 8).
           {
             destruct (le_gt_dec d 9).
             - left. assumption.
             - right.
               destruct (le_gt_dec k 8).
               + assumption.
               + (* d >= 10, k >= 9 implies d*k >= 90 > 83 *)
                 assert (d * k >= 10 * 9).
                 { apply Nat.mul_le_mono; lia. }
                 lia.
           }
           destruct H as [Hd | Hk_bound].
           ++ (* Case d <= 9 *)
              destruct d as [|d]. { rewrite Nat.mul_0_r in Hk. discriminate. }
              destruct d as [|d]. { left. reflexivity. } (* d=1 *)
              destruct d as [|d]. { exfalso. lia. } (* d=2 *)
              destruct d as [|d]. { exfalso. lia. } (* d=3 *)
              destruct d as [|d]. { exfalso. lia. } (* d=4 *)
              destruct d as [|d]. { exfalso. lia. } (* d=5 *)
              destruct d as [|d]. { exfalso. lia. } (* d=6 *)
              destruct d as [|d]. { exfalso. lia. } (* d=7 *)
              destruct d as [|d]. { exfalso. lia. } (* d=8 *)
              destruct d as [|d]. { exfalso. lia. } (* d=9 *)
              exfalso. lia.
           ++ (* Case k <= 8 *)
              destruct k as [|k]. { rewrite Nat.mul_0_l in Hk. discriminate. }
              destruct k as [|k]. { right. rewrite Nat.mul_1_l in Hk. symmetry. assumption. } (* k=1 *)
              destruct k as [|k]. { exfalso. lia. } (* k=2 *)
              destruct k as [|k]. { exfalso. lia. } (* k=3 *)
              destruct k as [|k]. { exfalso. lia. } (* k=4 *)
              destruct k as [|k]. { exfalso. lia. } (* k=5 *)
              destruct k as [|k]. { exfalso. lia. } (* k=6 *)
              destruct k as [|k]. { exfalso. lia. } (* k=7 *)
              destruct k as [|k]. { exfalso. lia. } (* k=8 *)
              exfalso. lia.
      * (* End of list *)
        constructor.
    + (* Part 3: Sorted check *)
      repeat constructor.
Qed.