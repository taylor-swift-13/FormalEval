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
  specialFilter_spec [-2%Z; 4%Z; 8%Z; 14%Z; 10%Z; -324%Z; 123%Z; 103%Z; 16%Z; 10%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* -2: 10 <? -2 = false, so special_number_b -2 = false *)
  (* 4: 10 <? 4 = false, so special_number_b 4 = false *)
  (* 8: 10 <? 8 = false, so special_number_b 8 = false *)
  (* 14: abs_n = 14, msd_fuel = 1, last_digit = 4, Z.odd 1 = true, Z.odd 4 = false, so special_number_b 14 = false *)
  (* 10: abs_n = 10, 10 <? 10 = false, so special_number_b 10 = false *)
  (* -324: abs_n = 324, msd_fuel = 3, last_digit = 4, Z.odd 3 = true, Z.odd 4 = false, so special_number_b -324 = false *)
  (* 123: abs_n = 123, msd_fuel = 1, last_digit = 3, Z.odd 1 = true, Z.odd 3 = true, so special_number_b 123 = true *)
  (* 103: abs_n = 103, msd_fuel = 1, last_digit = 3, Z.odd 1 = true, Z.odd 3 = true, so special_number_b 103 = true *)
  (* 16: abs_n = 16, msd_fuel = 1, last_digit = 6, Z.odd 1 = true, Z.odd 6 = false, so special_number_b 16 = false *)
  (* 10: abs_n = 10, 10 <? 10 = false, so special_number_b 10 = false *)
  reflexivity.
Qed.