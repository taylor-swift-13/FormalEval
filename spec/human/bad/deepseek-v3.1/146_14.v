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

Example test_case : problem_146_spec [14; -8; 62; 71; -123; 39] 2.
Proof.
  unfold problem_146_spec, specialFilter_impl.
  simpl.
  unfold special_number_b.
  repeat (simpl; unfold last_digit).
  replace (Z.abs 14) with 14 by reflexivity.
  replace (Z.abs (-8)) with 8 by reflexivity.
  replace (Z.abs 62) with 62 by reflexivity.
  replace (Z.abs 71) with 71 by reflexivity.
  replace (Z.abs (-123)) with 123 by reflexivity.
  replace (Z.abs 39) with 39 by reflexivity.
  simpl.
  (* Check each element whether it satisfies proper conditions *)
  (* 14: n > 10, msd and last digit odd? 14 is even, so no *)
  (* -8: n < 10, so skip main check, result depends on msd_fuel and last_digit, but since n<10, msd_fuel = n *)
  (* For -8: abs =8, 8<10, so msd_fuel=8, last_digit=8, even -> false *)
  (* 62: n>10, see if msd_fuel is odd: msd_fuel of 62 is 6, even -> false *)
  (* 71: n>10, msd=7 odd, last digit 1 odd -> true *)
  (* -123: abs=123, n>10, msd=1 odd, last_digit=3 odd -> true *)
  (* 39: n>10, msd=3 odd, last digit 9 odd -> true *)
  (* The true count is 3? But output=2, so need to check which satisfy. *)
  (* Review conditions carefully: the filter applies special_number_b which requires all three conditions: n>10, msd_fuel odd, last_digit odd*)
  (* Let's check the elements: *)
  (* 14: 14 >10? yes, 14 mod10=4 even, so Z.odd 4 = false -> exclude *)
  (* -8: abs=-8, abs=8<10, so msd_fuel=8, last_digit=8, even, exclude *)
  (* 62: >10, msd_fuel=6, even, exclude *)
  (* 71: >10, msd=7 odd, last_digit=1 odd, both odd -> include *)
  (* -123: abs=123, >10, msd_fuel=1 odd, last_digit=3 odd -> include *)
  (* 39: >10, msd=3 odd, last_digit=9 odd -> include *)
  (* So total: 3 elements satisfy. Output=2 indicates only 2 are counted, so perhaps filtering is not matching the above? *)
  (* Wait, the original spec is to count how many satisfy, and output=2, so filtering must yield 2 elements *)
  (* Checking the previous code for correctness might be better to just produce the proof, trusting the filter count. *)
  reflexivity.
Qed.
Qed