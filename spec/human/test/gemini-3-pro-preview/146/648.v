Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.Ascii.
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

(* 任意整数列表输入均可 *)
Definition problem_146_pre (nums : list Z) : Prop := True.

Definition problem_146_spec (nums : list Z) (output : Z) : Prop :=
  output = specialFilter_impl nums.

Example test_problem_146 : problem_146_spec [63; 15; 84; 75; -56; 21; 13; 15] 4.
Proof.
  unfold problem_146_spec.
  unfold specialFilter_impl.
  (* 
     Evaluating the filter:
     - 63: 10 < 63 (true), msd(63)=6 (even) -> false
     - 15: 10 < 15 (true), msd(15)=1 (odd), last(15)=5 (odd) -> true
     - 84: 10 < 84 (true), msd(84)=8 (even) -> false
     - 75: 10 < 75 (true), msd(75)=7 (odd), last(75)=5 (odd) -> true
     - -56: 10 < -56 (false) -> false
     - 21: 10 < 21 (true), msd(21)=2 (even) -> false
     - 13: 10 < 13 (true), msd(13)=1 (odd), last(13)=3 (odd) -> true
     - 15: (same as above) -> true
     Total count is 4.
  *)
  simpl.
  reflexivity.
Qed.