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

Example test_case_24 : problem_24_spec 28 14.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 28 mod 14 = 0 *)
    simpl. reflexivity.
  - split.
    + (* Goal 2: 14 < 28 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 28 -> 28 mod i = 0 -> i <= 14 *)
      intros i [Hpos Hlt] Hdiv.
      apply Nat.mod_divide in Hdiv; [| lia].
      destruct Hdiv as [k Hk].
      destruct (le_gt_dec i 14).
      * assumption.
      * (* Case i > 14 *)
        (* Since i > 14 and i divides 28, the quotient k must be < 2.
           Since i < 28, k must be > 1. This leads to a contradiction. *)
        destruct k.
        { (* k = 0 implies 28 = 0 *) simpl in Hk. discriminate. }
        destruct k.
        { (* k = 1 implies i = 28, contradicting i < 28 *) simpl in Hk. lia. }
        { (* k >= 2 *)
          assert (2 * i > 28) by lia.
          assert (S (S k) * i >= 2 * i).
          { apply Nat.mul_le_mono_r. lia. }
          lia.
        }
Qed.