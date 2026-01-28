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

Example test_case_24 : problem_24_spec 24 12.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 24 mod 12 = 0 *)
    simpl. reflexivity.
  - split.
    + (* Goal 2: 12 < 24 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 24 -> 24 mod i = 0 -> i <= 12 *)
      intros i [Hpos Hlt] Hdiv.
      destruct (le_gt_dec i 12); [assumption|].
      apply Nat.mod_divide in Hdiv; [|lia].
      destruct Hdiv as [k Hk].
      destruct k as [| [| k]].
      * (* k = 0 *)
        simpl in Hk. discriminate.
      * (* k = 1 *)
        simpl in Hk. lia.
      * (* k >= 2 *)
        rewrite Hk in Hlt.
        assert (Hge: S (S k) * i >= 2 * 13).
        { apply Nat.mul_le_mono; lia. }
        lia.
Qed.