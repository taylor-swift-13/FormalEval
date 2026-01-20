(* Required imports *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* Definition of last_digit *)
Definition last_digit (n : Z) : Z :=
  Z.abs (n mod 10).

(* Definition of msd_fuel *)
Fixpoint msd_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n mod 10
  | S f =>
    if Z_lt_dec n 10 then n
    else msd_fuel f (n / 10)
  end.

(* Definition of special_number_b *)
Definition special_number_b (n : Z) : bool :=
  let abs_n := Z.abs n in
  (10 <? n) && (Z.odd (msd_fuel (Z.to_nat abs_n) abs_n)) && (Z.odd (last_digit abs_n)).

(* Specification of specialFilter *)
Definition specialFilter_spec (nums : list Z) (output : Z) : Prop :=
  output = Z.of_nat (length (filter special_number_b nums)).

(* Test case *)
Example specialFilter_test :
  specialFilter_spec [15%Z; 84%Z; 75%Z; 8518%Z; -56%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 15: abs(15) = 15, 10 <? 15 = true, msd_fuel = 1, last_digit = 5, both odd, so special_number_b 15 = true *)
  (* 84: abs(84) = 84, 10 <? 84 = true, msd_fuel = 8, last_digit = 4, not both odd, so special_number_b 84 = false *)
  (* 75: abs(75) = 75, 10 <? 75 = true, msd_fuel = 7, last_digit = 5, both odd, so special_number_b 75 = true *)
  (* 8518: abs(8518) = 8518, 10 <? 8518 = true, msd_fuel = 8, last_digit = 8, not both odd, so special_number_b 8518 = false *)
  (* -56: abs(-56) = 56, 10 <? 56 = true, msd_fuel = 5, last_digit = 6, not both odd, so special_number_b -56 = false *)
  reflexivity.
Qed.