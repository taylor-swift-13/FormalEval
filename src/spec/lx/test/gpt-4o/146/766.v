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
  specialFilter_spec [-56%Z; -123%Z; 456%Z; 75%Z; 112%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* -56: abs(-56) = 56, 10 <? 56 = true, msd_fuel = 5, last_digit = 6, so special_number_b -56 = false *)
  (* -123: abs(-123) = 123, 10 <? 123 = true, msd_fuel = 1, last_digit = 3, so special_number_b -123 = true *)
  (* 456: 10 <? 456 = true, msd_fuel = 4, last_digit = 6, so special_number_b 456 = false *)
  (* 75: 10 <? 75 = true, msd_fuel = 7, last_digit = 5, so special_number_b 75 = false *)
  (* 112: 10 <? 112 = true, msd_fuel = 1, last_digit = 2, so special_number_b 112 = false *)
  reflexivity.
Qed.