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

Example test_factorize_55 : factorize_spec 55 [5; 11].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + constructor.
      * unfold is_prime. split.
        -- lia.
        -- intros d Hdiv.
           destruct d as [|d]. { destruct Hdiv as [x Hx]. simpl in Hx. discriminate. }
           destruct d as [|d]. { left. reflexivity. }
           destruct d as [|d]. { apply Nat.mod_divide in Hdiv; [simpl in Hdiv; discriminate | lia]. }
           destruct d as [|d]. { apply Nat.mod_divide in Hdiv; [simpl in Hdiv; discriminate | lia]. }
           destruct d as [|d]. { apply Nat.mod_divide in Hdiv; [simpl in Hdiv; discriminate | lia]. }
           destruct d as [|d]. { right. reflexivity. }
           apply Nat.divide_pos_le in Hdiv; lia.
      * constructor.
        -- unfold is_prime. split.
           ++ lia.
           ++ intros d Hdiv.
              destruct d as [|d]. { destruct Hdiv as [x Hx]. simpl in Hx. discriminate. }
              destruct d as [|d]. { left. reflexivity. }
              destruct d as [|d]. { apply Nat.mod_divide in Hdiv; [simpl in Hdiv; discriminate | lia]. }
              destruct d as [|d]. { apply Nat.mod_divide in Hdiv; [simpl in Hdiv; discriminate | lia]. }
              destruct d as [|d]. { apply Nat.mod_divide in Hdiv; [simpl in Hdiv; discriminate | lia]. }
              destruct d as [|d]. { apply Nat.mod_divide in Hdiv; [simpl in Hdiv; discriminate | lia]. }
              destruct d as [|d]. { apply Nat.mod_divide in Hdiv; [simpl in Hdiv; discriminate | lia]. }
              destruct d as [|d]. { apply Nat.mod_divide in Hdiv; [simpl in Hdiv; discriminate | lia]. }
              destruct d as [|d]. { apply Nat.mod_divide in Hdiv; [simpl in Hdiv; discriminate | lia]. }
              destruct d as [|d]. { apply Nat.mod_divide in Hdiv; [simpl in Hdiv; discriminate | lia]. }
              destruct d as [|d]. { apply Nat.mod_divide in Hdiv; [simpl in Hdiv; discriminate | lia]. }
              destruct d as [|d]. { right. reflexivity. }
              apply Nat.divide_pos_le in Hdiv; lia.
        -- constructor.
    + repeat constructor; lia.
Qed.