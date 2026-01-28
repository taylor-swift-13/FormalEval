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

Example test_case_24 : problem_24_spec 80 40.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 80 mod 40 = 0 *)
    simpl. reflexivity.
  - split.
    + (* Goal 2: 40 < 80 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 80 -> 80 mod i = 0 -> i <= 40 *)
      intros i [Hgt0 Hlt80] Hdiv.
      destruct (le_gt_dec i 40) as [Hle | Hgt].
      * (* Case i <= 40 *)
        assumption.
      * (* Case i > 40 *)
        apply Nat.mod_divide in Hdiv; try lia.
        destruct Hdiv as [k Hk].
        destruct k.
        { (* k = 0 *) simpl in Hk. discriminate. }
        destruct k.
        { (* k = 1 *) simpl in Hk. lia. }
        { (* k >= 2 *)
          assert (Hk2: S (S k) * i >= 2 * i).
          { simpl. lia. }
          rewrite <- Hk in Hk2.
          lia.
        }
Qed.