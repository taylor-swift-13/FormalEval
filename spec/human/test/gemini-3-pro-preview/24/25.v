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

Example test_case_24 : problem_24_spec 236 118.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 236 mod 118 = 0 *)
    reflexivity.
  - split.
    + (* Goal 2: 118 < 236 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 236 -> 236 mod i = 0 -> i <= 118 *)
      intros i [Hgt0 Hlt] Hdiv.
      apply Nat.mod_divides in Hdiv; [|lia].
      destruct Hdiv as [k Hk].
      (* Hk : 236 = i * k *)
      destruct k.
      * (* Case k = 0 *)
        rewrite Nat.mul_0_r in Hk. discriminate.
      * destruct k.
        -- (* Case k = 1 *)
           rewrite Nat.mul_1_r in Hk. subst. lia.
        -- (* Case k >= 2 *)
           (* 236 = i * S (S k) *)
           (* So i * 2 <= i * S (S k) = 236 *)
           assert (Hle: 2 * i <= 236).
           {
             rewrite Hk.
             rewrite (Nat.mul_comm i).
             apply Nat.mul_le_mono_r.
             lia.
           }
           lia.
Qed.