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
  specialFilter_spec [24%Z; -25%Z; 9%Z; 12%Z; 37%Z; -71%Z; -35%Z; -25%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 24: 10 <? 24 = true, msd_fuel 24 = 2, last_digit 24 = 4, so special_number_b 24 = false *)
  (* -25: 10 <? 25 = true, msd_fuel 25 = 2, last_digit 25 = 5, so special_number_b -25 = false *)
  (* 9: 10 <? 9 = false, so special_number_b 9 = false *)
  (* 12: 10 <? 12 = true, msd_fuel 12 = 1, last_digit 12 = 2, so special_number_b 12 = false *)
  (* 37: 10 <? 37 = true, msd_fuel 37 = 3, last_digit 37 = 7, so special_number_b 37 = true *)
  (* -71: 10 <? 71 = true, msd_fuel 71 = 7, last_digit 71 = 1, so special_number_b -71 = false *)
  (* -35: 10 <? 35 = true, msd_fuel 35 = 3, last_digit 35 = 5, so special_number_b -35 = false *)
  (* -25: 10 <? 25 = true, msd_fuel 25 = 2, last_digit 25 = 5, so special_number_b -25 = false *)
  reflexivity.
Qed.