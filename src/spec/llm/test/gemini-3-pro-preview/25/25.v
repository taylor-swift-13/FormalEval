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

Example test_factorize_34 : factorize_spec 34 [2; 17].
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
        -- (* 2 > 1 *)
           lia.
        -- (* Divisors check *)
           intros d Hdiv.
           destruct d as [|d].
           ++ (* d = 0 *)
              destruct Hdiv as [z Hz].
              rewrite Nat.mul_0_r in Hz.
              discriminate.
           ++ destruct d as [|d].
              ** (* d = 1 *)
                 left. reflexivity.
              ** destruct d as [|d].
                 --- (* d = 2 *)
                     right. reflexivity.
                 --- (* d >= 3 *)
                     apply Nat.divide_pos_le in Hdiv; try lia.
      * (* Next prime: 17 *)
        constructor.
        -- (* is_prime 17 *)
           unfold is_prime. split.
           ++ (* 17 > 1 *)
              lia.
           ++ (* Divisors check *)
              intros d Hdiv.
              assert (d <= 17). { apply Nat.divide_pos_le in Hdiv; lia. }
              (* Check d = 0 *)
              destruct d as [|d]. { destruct Hdiv as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate. }
              (* Check d = 1 *)
              destruct d as [|d]. { left. reflexivity. }
              (* Check d = 2 to 16 *)
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              destruct d as [|d]. { exfalso. apply Nat.mod_divide in Hdiv; [|lia]. simpl in Hdiv. discriminate. }
              (* Check d = 17 *)
              destruct d as [|d]. { right. reflexivity. }
              (* Check d > 17 *)
              lia.
        -- (* End of list *)
           constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; lia.
Qed.