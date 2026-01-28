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

Example test_case_24 : problem_24_spec 234 117.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 234 mod 117 = 0 *)
    reflexivity.
  - split.
    + (* Goal 2: 117 < 234 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 234 -> 234 mod i = 0 -> i <= 117 *)
      intros i [Hpos Hlt] Hdiv.
      (* Use divisibility property: 234 mod i = 0 <-> exists k, 234 = i * k *)
      apply Nat.mod_divide in Hdiv; [|lia].
      destruct Hdiv as [k Hk].
      (* Analyze k *)
      destruct k.
      * (* Case k = 0: 234 = i * 0 = 0, contradiction *)
        simpl in Hk. discriminate.
      * destruct k.
        -- (* Case k = 1: 234 = i * 1 = i, contradiction with i < 234 *)
           simpl in Hk. rewrite <- Hk in Hlt. lia.
        -- (* Case k >= 2: 234 = i * (S (S k)) *)
           (* i * 2 <= i * (S (S k)) = 234 *)
           assert (Hmul: i * 2 <= i * S (S k)).
           { apply Nat.mul_le_mono_l. lia. }
           rewrite <- Hk in Hmul.
           (* 234 = 117 * 2 *)
           assert (H234: 234 = 117 * 2) by reflexivity.
           rewrite H234 in Hmul.
           (* i * 2 <= 117 * 2 implies i <= 117 *)
           apply Nat.mul_le_mono_pos_r in Hmul; [assumption|lia].
Qed.