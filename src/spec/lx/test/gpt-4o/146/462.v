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
  specialFilter_spec [-324%Z; 4%Z; 8%Z; 11%Z; 6%Z; 11%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* -324: abs(-324) = 324, 10 <? 324 = true, msd_fuel (Z.to_nat 324) 324 = 3, Z.odd 3 = true, last_digit 324 = 4, Z.odd 4 = false, so special_number_b -324 = false *)
  (* 4: abs(4) = 4, 10 <? 4 = false, so special_number_b 4 = false *)
  (* 8: abs(8) = 8, 10 <? 8 = false, so special_number_b 8 = false *)
  (* 11: abs(11) = 11, 10 <? 11 = true, msd_fuel (Z.to_nat 11) 11 = 1, Z.odd 1 = true, last_digit 11 = 1, Z.odd 1 = true, so special_number_b 11 = true *)
  (* 6: abs(6) = 6, 10 <? 6 = false, so special_number_b 6 = false *)
  (* 11: abs(11) = 11, 10 <? 11 = true, msd_fuel (Z.to_nat 11) 11 = 1, Z.odd 1 = true, last_digit 11 = 1, Z.odd 1 = true, so special_number_b 11 = true *)
  reflexivity.
Qed.