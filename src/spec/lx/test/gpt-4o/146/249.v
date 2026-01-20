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
  specialFilter_spec [112%Z; -324%Z; 456%Z; 1111%Z; 7113%Z; 456%Z; 100%Z; 63%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 112: 10 <? 112 = true, msd_fuel 112 = 1, last_digit 112 = 2, so special_number_b 112 = false *)
  (* -324: 10 <? 324 = true, msd_fuel 324 = 3, last_digit 324 = 4, so special_number_b -324 = false *)
  (* 456: 10 <? 456 = true, msd_fuel 456 = 4, last_digit 456 = 6, so special_number_b 456 = false *)
  (* 1111: 10 <? 1111 = true, msd_fuel 1111 = 1, last_digit 1111 = 1, so special_number_b 1111 = true *)
  (* 7113: 10 <? 7113 = true, msd_fuel 7113 = 7, last_digit 7113 = 3, so special_number_b 7113 = true *)
  (* 456: 10 <? 456 = true, msd_fuel 456 = 4, last_digit 456 = 6, so special_number_b 456 = false *)
  (* 100: 10 <? 100 = true, msd_fuel 100 = 1, last_digit 100 = 0, so special_number_b 100 = false *)
  (* 63: 10 <? 63 = true, msd_fuel 63 = 6, last_digit 63 = 3, so special_number_b 63 = false *)
  reflexivity.
Qed.