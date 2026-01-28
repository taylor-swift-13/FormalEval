Require Import Arith.
Require Import Lia.

(* Pre: require `input >= 2` so that a largest proper divisor exists *)
Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  (* 1. output is a divisor of input *)
  input mod output = 0 /\

  (* 2. output is strictly less than input *)
  output < input /\

  (* 3. for any divisor i strictly less than input, i <= output *)
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example test_case_24 : problem_24_spec 22 11.
Proof.
  unfold problem_24_spec.
  split.
  - simpl. reflexivity.
  - split.
    + lia.
    + intros i [Hgt0 Hlt22] Hdiv.
      destruct (le_gt_dec i 11) as [Hle | Hgt].
      * assumption.
      * apply Nat.mod_divide in Hdiv; [| lia].
        destruct Hdiv as [k Hk].
        destruct k.
        -- simpl in Hk. discriminate.
        -- destruct k.
           ++ simpl in Hk. rewrite Hk in Hlt22. lia.
           ++ assert (Hge2: S (S k) >= 2) by lia.
              assert (Hge12: i >= 12) by lia.
              assert (Hprod: S (S k) * i >= 2 * 12).
              { apply Nat.mul_le_mono; assumption. }
              rewrite <- Hk in Hprod.
              simpl in Hprod.
              lia.
Qed.