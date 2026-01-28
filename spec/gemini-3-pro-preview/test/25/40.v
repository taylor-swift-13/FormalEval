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

Example test_factorize_27 : factorize_spec 27 [3; 3; 3].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + assert (H3: is_prime 3).
      {
        unfold is_prime. split.
        - lia.
        - intros d Hdiv.
          destruct d as [| [| [| [| d'] ]]].
          + destruct Hdiv as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate.
          + left. reflexivity.
          + destruct Hdiv as [q Hq].
            destruct q as [| [| q']].
            * simpl in Hq. discriminate.
            * simpl in Hq. discriminate.
            * simpl in Hq. lia.
          + right. reflexivity.
          + apply Nat.divide_pos_le in Hdiv; try lia.
      }
      repeat (constructor; try exact H3).
    + repeat constructor.
Qed.