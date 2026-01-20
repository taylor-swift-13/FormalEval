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
  specialFilter_spec [63%Z; 24%Z; 84%Z; 615%Z; 75%Z; -56%Z; 13%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 63: 10 <? 63 = true, msd_fuel 63 = 6, last_digit 63 = 3, special_number_b 63 = false *)
  (* 24: 10 <? 24 = true, msd_fuel 24 = 2, last_digit 24 = 4, special_number_b 24 = false *)
  (* 84: 10 <? 84 = true, msd_fuel 84 = 8, last_digit 84 = 4, special_number_b 84 = false *)
  (* 615: 10 <? 615 = true, msd_fuel 615 = 6, last_digit 615 = 5, special_number_b 615 = false *)
  (* 75: 10 <? 75 = true, msd_fuel 75 = 7, last_digit 75 = 5, special_number_b 75 = true *)
  (* -56: 10 <? 56 = true, msd_fuel 56 = 5, last_digit 56 = 6, special_number_b 56 = false *)
  (* 13: 10 <? 13 = true, msd_fuel 13 = 1, last_digit 13 = 3, special_number_b 13 = true *)
  reflexivity.
Qed.