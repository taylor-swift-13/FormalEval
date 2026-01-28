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

Example test_factorize_37 : factorize_spec 37 [37].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           assert (Hle: d <= 37).
           { apply Nat.divide_pos_le; [lia | assumption]. }
           do 37 (destruct d as [|d]; [
             try (left; reflexivity);
             try (exfalso; destruct Hdiv as [k Hk]; simpl in Hk; lia)
           | ]).
           destruct d; [ right; reflexivity | exfalso; lia ].
      * constructor.
    + repeat constructor.
Qed.