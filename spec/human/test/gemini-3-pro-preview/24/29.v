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

Example test_case_24 : problem_24_spec 76 38.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 76 mod 38 = 0 *)
    reflexivity.
  - split.
    + (* Goal 2: 38 < 76 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 76 -> 76 mod i = 0 -> i <= 38 *)
      intros i [Hgt0 Hlt76] Hdiv.
      (* Convert divisibility to multiplication: 76 = i * k *)
      (* Using Nat.div_exact instead of deprecated Nat.mod_divide *)
      apply Nat.div_exact in Hdiv; [| lia].
      remember (76 / i) as k.
      (* Hdiv is now 76 = i * k *)
      
      (* Analyze k. Since i < 76, k must be >= 2 *)
      assert (Hk_ge_2: k >= 2).
      {
        destruct k.
        - (* k = 0 => 76 = 0 *)
          simpl in Hdiv; lia.
        - destruct k.
          + (* k = 1 => 76 = i, contradicts i < 76 *)
            simpl in Hdiv; rewrite Nat.mul_1_r in Hdiv; subst; lia.
          + (* k >= 2 *)
            lia.
      }
      
      (* i * 2 <= i * k = 76 *)
      assert (Hi2: i * 2 <= 76).
      {
        rewrite Hdiv.
        apply Nat.mul_le_mono_l.
        lia.
      }
      
      (* i * 2 <= 76 implies i <= 38 *)
      lia.
Qed.