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

Example test_factorize_51 : factorize_spec 51 [3; 17].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [|d]. { destruct Hdiv; lia. }
           destruct d as [|d]. { left. reflexivity. }
           destruct d as [|d]. { exfalso. destruct Hdiv as [q Hq]; simpl in Hq; lia. }
           destruct d as [|d]. { right. reflexivity. }
           apply Nat.divide_pos_le in Hdiv; try lia.
      * constructor.
        -- unfold is_prime. split.
           ++ lia.
           ++ intros d Hdiv.
              destruct d as [|d]. { destruct Hdiv; lia. }
              destruct d as [|d]. { left. reflexivity. }
              do 15 (destruct d as [|d]; [ exfalso; destruct Hdiv as [q Hq]; simpl in Hq; lia | ]).
              destruct d as [|d]. { right. reflexivity. }
              apply Nat.divide_pos_le in Hdiv; try lia.
        -- constructor.
    + repeat constructor.
Qed.