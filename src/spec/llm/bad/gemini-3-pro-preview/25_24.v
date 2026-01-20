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

Example test_factorize_14 : factorize_spec 14 [2; 7].
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
        -- lia.
        -- intros d Hdiv.
           destruct d as [|d].
           ++ destruct Hdiv as [z Hz]. simpl in Hz. discriminate.
           ++ destruct d as [|d].
              ** left. reflexivity.
              ** destruct d as [|d].
                 --- right. reflexivity.
                 --- apply Nat.divide_pos_le in Hdiv; try lia.
      * constructor.
        -- (* is_prime 7 *)
           unfold is_prime. split.
           ++ lia.
           ++ intros d Hdiv.
              destruct d as [|d].
              ** destruct Hdiv as [z Hz]. simpl in Hz. discriminate.
              ** destruct d as [|d].
                 --- left. reflexivity.
                 --- destruct d as [|d].
                     *** destruct Hdiv as [k Hk]. simpl in Hk. lia.
                     *** destruct d as [|d].
                         ---- destruct Hdiv as [k Hk]. simpl in Hk. lia.
                         ---- destruct d as [|d].
                              ***** destruct Hdiv as [k Hk]. simpl in Hk. lia.
                              ***** destruct d as [|d].
                                    ----- destruct Hdiv as [k Hk]. simpl in Hk. lia.
                                    ----- destruct d as [|d].
                                          **** destruct Hdiv as [k Hk]. simpl in Hk. lia.
                                          **** destruct d as [|d].
                                               ---- right. reflexivity.
                                               ---- apply Nat.divide_pos_le in Hdiv; try lia.
        -- constructor.
    + (* Part 3: Sorted check *)
      repeat constructor; simpl; try lia.
Qed.