Require Import Coq.Lists.List Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition last_digit (n : Z) : Z := Z.abs (n mod 10).

Fixpoint msd_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n mod 10
  | S f => if Z_lt_dec n 10 then n else msd_fuel f (n/10)
  end.

Definition special_number_b (n : Z) : bool :=
  let abs_n := Z.abs n in (10 <? n) && (Z.odd (msd_fuel (Z.to_nat abs_n) abs_n)) && (Z.odd (last_digit abs_n)).

Definition specialFilter_impl (nums : list Z) : Z := Z.of_nat (length (filter special_number_b nums)).

Definition problem_146_pre (nums : list Z) : Prop := True.

Definition problem_146_spec (nums : list Z) (output : Z) : Prop :=
  output = specialFilter_impl nums.

Example test_case : problem_146_spec [57; -15; 42; 99; 56; 104; 42] 2.
Proof.
  unfold problem_146_spec, specialFilter_impl.
  simpl.
  unfold special_number_b.
  repeat (
    simpl; unfold last_digit
  ).
  (* Manually evaluate filter: *)
  (* Check each element: *)
  (* 57: 10<? 57 true, msd of abs 57 is 5 (odd), last digit 7 (odd) -> true *)
  (* -15: 10<? -15 false -> false *)
  (* 42: 10<? 42 true, msd abs is 4 (even), -> false *)
  (* 99: 10<? 99 true, msd 9 (odd), last 9 (odd) -> true *)
  (* 56: 10<? 56 true, msd 5 (odd), last 6 (even) -> false *)
  (* 104: 10<? 104 true, msd 1 (odd), last 4 (even) -> false *)
  (* 42 (second): same as before, 42 -> false *)
  (* So total true elements: 57 and 99, count = 2 *)
  reflexivity.
Qed.