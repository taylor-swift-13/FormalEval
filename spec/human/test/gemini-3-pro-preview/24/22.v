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

Example test_case_24 : problem_24_spec 23 1.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 23 mod 1 = 0 *)
    simpl. reflexivity.
  - split.
    + (* Goal 2: 1 < 23 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 23 -> 23 mod i = 0 -> i <= 1 *)
      intros i [Hgt0 Hlt23] Hdiv.
      (* Handle i = 0 (contradiction with Hgt0) *)
      destruct i as [|i]; [ lia | ].
      (* Handle i = 1 (goal holds: 1 <= 1) *)
      destruct i as [|i]; [ lia | ].
      (* Check cases i = 2 to i = 22 *)
      (* Since 23 is prime, no i in [2, 22] divides 23 *)
      do 21 (destruct i as [|i]; [ simpl in Hdiv; discriminate | ]).
      (* Remaining cases where i >= 23 (contradiction with Hlt23) *)
      lia.
Qed.