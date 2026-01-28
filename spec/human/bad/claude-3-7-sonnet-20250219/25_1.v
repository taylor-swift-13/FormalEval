Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_25_spec (input : nat) (output : list nat) : Prop :=
  Sorted le output /\
  fold_right Nat.mul 1 output = input /\
  Forall IsPrime output.

Example test_factorize_2 :
  problem_25_spec 2 [2].
Proof.
  unfold problem_25_spec.
  split.
  - (* Sorted le [2] *)
    simpl. constructor.
    + omega.
    + constructor.
  - split.
    + (* fold_right Nat.mul 1 [2] = 2 *)
      simpl. reflexivity.
    + (* Forall IsPrime [2] *)
      simpl.
      unfold IsPrime.
      split.
      * omega.
      * intros d Hmod.
        destruct d as [|d'].
        -- simpl in Hmod. rewrite Nat.mod_0_l in Hmod; try omega.
        -- destruct d'.
           ++ left. reflexivity.
           ++ right.
              assert (Hmod2 := Hmod).
              rewrite Nat.mod_same in Hmod2 by omega.
              apply Nat.mod_divide in Hmod2; try omega.
              destruct Hmod2 as [k Hk].
              simpl in Hk.
              (* Since 2 = d * k, and d >= 2, k = 1 and d = 2 *)
              assert (k = 1).
              {
                rewrite <- Hk.
                apply Nat.mul_le_mono_pos_l with (p:=d) in Hk; omega.
              }
              subst k.
              reflexivity.
Qed.