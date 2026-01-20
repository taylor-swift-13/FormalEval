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
  specialFilter_spec [12%Z; 103%Z; 1892%Z; 15%Z; 15%Z; 1892%Z; 1892%Z; 1892%Z] 3%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 12: 10 <? 12 = true, msd_fuel 12 = 1, last_digit 12 = 2, so special_number_b 12 = false *)
  (* 103: 10 <? 103 = true, msd_fuel 103 = 1, last_digit 103 = 3, so special_number_b 103 = true *)
  (* 1892: 10 <? 1892 = true, msd_fuel 1892 = 1, last_digit 1892 = 2, so special_number_b 1892 = false *)
  (* 15: 10 <? 15 = true, msd_fuel 15 = 1, last_digit 15 = 5, so special_number_b 15 = true *)
  (* 15: 10 <? 15 = true, msd_fuel 15 = 1, last_digit 15 = 5, so special_number_b 15 = true *)
  (* 1892: 10 <? 1892 = true, msd_fuel 1892 = 1, last_digit 1892 = 2, so special_number_b 1892 = false *)
  (* 1892: 10 <? 1892 = true, msd_fuel 1892 = 1, last_digit 1892 = 2, so special_number_b 1892 = false *)
  (* 1892: 10 <? 1892 = true, msd_fuel 1892 = 1, last_digit 1892 = 2, so special_number_b 1892 = false *)
  reflexivity.
Qed.