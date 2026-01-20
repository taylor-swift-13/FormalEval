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
  specialFilter_spec [15%Z; -73%Z; 14%Z; -15%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 15: abs(15) = 15, 10 <? 15 = true, msd_fuel 15 = 1 (odd), last_digit 15 = 5 (odd), so special_number_b 15 = true *)
  (* -73: abs(-73) = 73, 10 <? 73 = true, msd_fuel 73 = 7 (odd), last_digit 73 = 3 (odd), so special_number_b -73 = true *)
  (* 14: abs(14) = 14, 10 <? 14 = true, msd_fuel 14 = 1 (odd), last_digit 14 = 4 (even), so special_number_b 14 = false *)
  (* -15: abs(-15) = 15, 10 <? 15 = true, msd_fuel 15 = 1 (odd), last_digit 15 = 5 (odd), so special_number_b -15 = true *)
  reflexivity.
Qed.