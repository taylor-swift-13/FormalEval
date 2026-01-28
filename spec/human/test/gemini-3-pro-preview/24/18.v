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

Example test_case_24 : problem_24_spec 73 1.
Proof.
  unfold problem_24_spec.
  split.
  - simpl. reflexivity.
  - split.
    + lia.
    + intros i [Hgt Hlt] Hdiv.
      (* Handle cases 0 and 1 *)
      destruct i as [|i]. lia.
      destruct i as [|i]. lia.
      (* Handle cases 2 through 72 *)
      do 71 (destruct i as [|i]; [ simpl in Hdiv; discriminate Hdiv | apply Nat.succ_lt_mono in Hlt ]).
      (* Remaining cases violate the upper bound *)
      lia.
Qed.