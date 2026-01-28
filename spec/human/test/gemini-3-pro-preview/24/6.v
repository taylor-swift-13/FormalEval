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

Example test_case_24 : problem_24_spec 2 1.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 2 mod 1 = 0 *)
    simpl. reflexivity.
  - split.
    + (* Goal 2: 1 < 2 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 2 -> 2 mod i = 0 -> i <= 1 *)
      intros i [Hgt0 Hlt2] Hdiv.
      (* Since 0 < i < 2, i can only be 1 *)
      assert (i = 1) as Hi by lia.
      subst.
      lia.
Qed.