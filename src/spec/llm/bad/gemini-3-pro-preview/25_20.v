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

Example test_factorize_11 : factorize_spec 11 [11].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * unfold is_prime. split.
        -- lia.
        -- intros d [k Hk].
           destruct d as [|d]. { lia. }
           destruct d as [|d]. { left. reflexivity. }
           destruct d as [|d]. { nia. }
           destruct d as [|d]. { nia. }
           destruct d as [|d]. { nia. }
           destruct d as [|d]. { nia. }
           destruct d as [|d]. { nia. }
           destruct d as [|d]. { nia. }
           destruct d as [|d]. { nia. }
           destruct d as [|d]. { nia. }
           destruct d as [|d]. { nia. }
           destruct d as [|d]. { right. reflexivity. }
           lia.
      * constructor.
    + repeat constructor.
Qed.