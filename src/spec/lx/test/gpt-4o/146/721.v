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
  specialFilter_spec [33%Z; -2%Z; -3%Z; 21%Z; 109%Z; 123%Z; 1892%Z] 3%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 33: abs(33) = 33, 10 <? 33 = true, msd_fuel 33 = 3, last_digit 33 = 3, both odd, so special_number_b 33 = true *)
  (* -2: abs(-2) = 2, 10 <? 2 = false, so special_number_b -2 = false *)
  (* -3: abs(-3) = 3, 10 <? 3 = false, so special_number_b -3 = false *)
  (* 21: abs(21) = 21, 10 <? 21 = true, msd_fuel 21 = 2, last_digit 21 = 1, last_digit odd but msd_fuel not odd, so special_number_b 21 = false *)
  (* 109: abs(109) = 109, 10 <? 109 = true, msd_fuel 109 = 1, last_digit 109 = 9, both odd, so special_number_b 109 = true *)
  (* 123: abs(123) = 123, 10 <? 123 = true, msd_fuel 123 = 1, last_digit 123 = 3, both odd, so special_number_b 123 = true *)
  (* 1892: abs(1892) = 1892, 10 <? 1892 = true, msd_fuel 1892 = 1, last_digit 1892 = 2, last_digit not odd, so special_number_b 1892 = false *)
  reflexivity.
Qed.