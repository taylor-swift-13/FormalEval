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

Example test_case_24 : problem_24_spec 72 36.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 72 mod 36 = 0 *)
    reflexivity.
  - split.
    + (* Goal 2: 36 < 72 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 72 -> 72 mod i = 0 -> i <= 36 *)
      intros i [Hgt0 Hlt72] Hdiv.
      (* 72 mod i = 0 implies 72 = i * (72 / i) *)
      apply Nat.div_exact in Hdiv; [|lia].
      remember (72 / i) as k.
      (* 72 = i * k. Since i < 72, k must be >= 2 *)
      assert (k >= 2).
      {
        destruct k.
        - (* k = 0 implies 72 = 0 *)
          rewrite Nat.mul_0_r in Hdiv. discriminate.
        - destruct k.
          + (* k = 1 implies 72 = i, contradicts i < 72 *)
            rewrite Nat.mul_1_r in Hdiv. subst. lia.
          + (* k >= 2 *)
            lia.
      }
      (* Since k >= 2, i * 2 <= i * k = 72 *)
      assert (i * 2 <= 72).
      { rewrite Hdiv. apply Nat.mul_le_mono_l. lia. }
      lia.
Qed.