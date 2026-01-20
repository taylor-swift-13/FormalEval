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
  specialFilter_spec [24%Z; -57%Z; 84%Z; 75%Z; -56%Z; 24%Z; -56%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 24: msd_fuel = 2, last_digit = 4, special_number_b = false *)
  (* -57: msd_fuel = 5, last_digit = 7, special_number_b = true *)
  (* 84: msd_fuel = 8, last_digit = 4, special_number_b = false *)
  (* 75: msd_fuel = 7, last_digit = 5, special_number_b = false *)
  (* -56: msd_fuel = 5, last_digit = 6, special_number_b = false *)
  (* 24: msd_fuel = 2, last_digit = 4, special_number_b = false *)
  (* -56: msd_fuel = 5, last_digit = 6, special_number_b = false *)
  reflexivity.
Qed.