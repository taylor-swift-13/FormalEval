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
  specialFilter_spec [11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 16%Z; 14%Z] 3%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 11: 10 <? 11 = true, msd_fuel 11 = 1, last_digit 11 = 1, so special_number_b 11 = true *)
  (* 12: 10 <? 12 = true, msd_fuel 12 = 1, last_digit 12 = 2, so special_number_b 12 = false *)
  (* 13: 10 <? 13 = true, msd_fuel 13 = 1, last_digit 13 = 3, so special_number_b 13 = true *)
  (* 14: 10 <? 14 = true, msd_fuel 14 = 1, last_digit 14 = 4, so special_number_b 14 = false *)
  (* 15: 10 <? 15 = true, msd_fuel 15 = 1, last_digit 15 = 5, so special_number_b 15 = true *)
  (* 16: 10 <? 16 = true, msd_fuel 16 = 1, last_digit 16 = 6, so special_number_b 16 = false *)
  (* 16: 10 <? 16 = true, msd_fuel 16 = 1, last_digit 16 = 6, so special_number_b 16 = false *)
  (* 14: 10 <? 14 = true, msd_fuel 14 = 1, last_digit 14 = 4, so special_number_b 14 = false *)
  reflexivity.
Qed.