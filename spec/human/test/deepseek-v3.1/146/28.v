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

Example test_case : problem_146_spec [24; -25; 9; 37; -71; -35; -25] 1.
Proof.
  unfold problem_146_spec, specialFilter_impl.
  simpl.
  unfold special_number_b.
  repeat (simpl; unfold last_digit).
  (* Compute the filter results step-by-step *)
  (* Checking each number:
     24: n = 24 > 10, msd = 2 (msd_fuel), last_digit = 4, n > 10, msd and last_digit odd? 2 and 4 are not odd -> false
     -25: n = -25, abs = 25, n > 10, msd = 2 (from 25), last_digit = 5, msd odd? 2 -> false, last_digit odd? 5 -> true, but overall false
     9: n = 9, n < 10, so msd_fuel (fuel=0) = 9, check n > 10? no, so false
     37: n=37 >10, msd=3, last_digit=7, both odd? 3 and 7 -> true
     -71: abs=71, n>10, msd=7, last_digit=1, both odd -> true
     -35: abs=35, n>10, msd=3, last_digit=5, both odd -> true
     -25: same as above, not all conditions hold for first part, but wait, check carefully:
       -25: abs=25, n>10, msd=2, last_digit=5, 2 is not odd -> false
  *)
  simpl.
  reflexivity.
Qed.