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

Example test_case_24 : problem_24_spec 500 250.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 500 mod 250 = 0 *)
    reflexivity.
  - split.
    + (* Goal 2: 250 < 500 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 500 -> 500 mod i = 0 -> i <= 250 *)
      intros i [Hpos Hlt] Hdiv.
      apply Nat.mod_divides in Hdiv; [|lia].
      destruct Hdiv as [k Hk].
      (* Hk: 500 = i * k *)
      destruct k as [|k'].
      * (* Case k = 0 *)
        rewrite Nat.mul_0_r in Hk. discriminate Hk.
      * destruct k' as [|k''].
        -- (* Case k = 1 *)
           rewrite Nat.mul_1_r in Hk. subst i.
           lia. (* i = 500 contradicts i < 500 *)
        -- (* Case k >= 2 *)
           (* We have 500 = i * S (S k'') *)
           assert (Hineq: i * 2 <= i * S (S k'')).
           { apply Nat.mul_le_mono_l. lia. }
           rewrite <- Hk in Hineq.
           lia.
Qed.