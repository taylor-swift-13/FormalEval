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

Example test_case_24 : problem_24_spec 100 50.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 100 mod 50 = 0 *)
    simpl. reflexivity.
  - split.
    + (* Goal 2: 50 < 100 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 100 -> 100 mod i = 0 -> i <= 50 *)
      intros i [Hgt0 Hlt100] Hdiv.
      (* Use divisibility property *)
      apply Nat.mod_divide in Hdiv; [| lia].
      destruct Hdiv as [k Hk].
      (* 100 = k * i. Since i < 100, k must be >= 2 *)
      assert (k >= 2).
      {
        destruct k.
        - (* k = 0 implies 100 = 0 *)
          simpl in Hk. discriminate.
        - destruct k.
          + (* k = 1 implies 100 = i, contradiction with i < 100 *)
            simpl in Hk. rewrite Hk in Hlt100. lia.
          + (* k >= 2 *)
            lia.
      }
      (* k >= 2 implies k * i >= 2 * i *)
      assert (100 >= 2 * i).
      {
        rewrite Hk.
        apply Nat.mul_le_mono_r.
        lia.
      }
      (* 100 >= 2 * i implies i <= 50 *)
      lia.
Qed.