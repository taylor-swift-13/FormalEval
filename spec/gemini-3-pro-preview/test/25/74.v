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

Example test_factorize_53 : factorize_spec 53 [53].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * unfold is_prime. split.
        -- lia.
        -- intros d [k Hk].
           destruct d as [|d].
           ++ rewrite Nat.mul_0_r in Hk. discriminate.
           ++ destruct d as [|d].
              ** left. reflexivity.
              ** right.
                 destruct k as [|k].
                 { rewrite Nat.mul_0_l in Hk. discriminate. }
                 destruct k as [|k].
                 { rewrite Nat.mul_1_l in Hk. rewrite Hk. reflexivity. }
                 exfalso.
                 do 26 (destruct k as [|k]; [ simpl in Hk; try lia | ]).
                 simpl in Hk. nia.
      * constructor.
    + repeat constructor.
Qed.