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
  specialFilter_spec [14%Z; -8%Z; 62%Z; 71%Z; -123%Z; 39%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 14: abs 14 = 14, 10 <? 14 = true, msd_fuel (Z.to_nat 14) 14 = 1 (odd), last_digit 14 = 4 (even), so special_number_b 14 = false *)
  (* -8: abs -8 = 8, 10 <? 8 = false, so special_number_b -8 = false *)
  (* 62: abs 62 = 62, 10 <? 62 = true, msd_fuel (Z.to_nat 62) 62 = 6 (even), so special_number_b 62 = false *)
  (* 71: abs 71 = 71, 10 <? 71 = true, msd_fuel (Z.to_nat 71) 71 = 7 (odd), last_digit 71 = 1 (odd), so special_number_b 71 = true *)
  (* -123: abs -123 = 123, 10 <? 123 = true, msd_fuel (Z.to_nat 123) 123 = 1 (odd), last_digit 123 = 3 (odd), so special_number_b -123 = true *)
  (* 39: abs 39 = 39, 10 <? 39 = true, msd_fuel (Z.to_nat 39) 39 = 3 (odd), last_digit 39 = 9 (odd), so special_number_b 39 = true *)
  reflexivity.
Qed.