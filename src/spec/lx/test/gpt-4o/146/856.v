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
  specialFilter_spec [790%Z; -124%Z; 789%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 790: abs(790) = 790, msd_fuel 790 = 7, last_digit 790 = 0, Z.odd 7 = true, Z.odd 0 = false, so special_number_b 790 = false *)
  (* -124: abs(-124) = 124, msd_fuel 124 = 1, last_digit 124 = 4, Z.odd 1 = true, Z.odd 4 = false, so special_number_b -124 = false *)
  (* 789: abs(789) = 789, msd_fuel 789 = 7, last_digit 789 = 9, Z.odd 7 = true, Z.odd 9 = true, so special_number_b 789 = true *)
  reflexivity.
Qed.