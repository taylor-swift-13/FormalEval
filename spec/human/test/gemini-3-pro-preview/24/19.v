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

Example test_case_24 : problem_24_spec 998 499.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 998 mod 499 = 0 *)
    simpl. reflexivity.
  - split.
    + (* Goal 2: 499 < 998 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 998 -> 998 mod i = 0 -> i <= 499 *)
      intros i [Hgt0 Hlt] Hdiv.
      apply Nat.mod_divide in Hdiv; [|lia].
      destruct Hdiv as [k Hk].
      (* Since i < 998 and 998 = k * i, k must be >= 2 *)
      assert (Hk_ge_2 : k >= 2).
      {
        destruct k.
        - (* k = 0 *) simpl in Hk. discriminate.
        - destruct k.
          + (* k = 1 *) simpl in Hk. lia.
          + (* k >= 2 *) lia.
      }
      (* 998 = k * i >= 2 * i -> i <= 499 *)
      rewrite Hk in *.
      assert (2 * i <= k * i).
      { apply Nat.mul_le_mono_r. lia. }
      lia.
Qed.