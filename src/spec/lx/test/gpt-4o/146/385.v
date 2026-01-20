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
  specialFilter_spec [121%Z; 120%Z; 121%Z; 122%Z; 214%Z; 357%Z; 8518%Z; 21517%Z; 2123%Z; 918%Z; 21517%Z] 3%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 121: 10 <? 121 = true, msd_fuel 121 = 1, last_digit 121 = 1, so special_number_b 121 = true *)
  (* 120: 10 <? 120 = true, msd_fuel 120 = 1, last_digit 120 = 0, so special_number_b 120 = false *)
  (* 121: 10 <? 121 = true, msd_fuel 121 = 1, last_digit 121 = 1, so special_number_b 121 = true *)
  (* 122: 10 <? 122 = true, msd_fuel 122 = 1, last_digit 122 = 2, so special_number_b 122 = false *)
  (* 214: 10 <? 214 = true, msd_fuel 214 = 2, last_digit 214 = 4, so special_number_b 214 = false *)
  (* 357: 10 <? 357 = true, msd_fuel 357 = 3, last_digit 357 = 7, so special_number_b 357 = true *)
  (* 8518: 10 <? 8518 = true, msd_fuel 8518 = 8, last_digit 8518 = 8, so special_number_b 8518 = false *)
  (* 21517: 10 <? 21517 = true, msd_fuel 21517 = 2, last_digit 21517 = 7, so special_number_b 21517 = false *)
  (* 2123: 10 <? 2123 = true, msd_fuel 2123 = 2, last_digit 2123 = 3, so special_number_b 2123 = false *)
  (* 918: 10 <? 918 = true, msd_fuel 918 = 9, last_digit 918 = 8, so special_number_b 918 = false *)
  (* 21517: 10 <? 21517 = true, msd_fuel 21517 = 2, last_digit 21517 = 7, so special_number_b 21517 = false *)
  reflexivity.
Qed.