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
  specialFilter_spec [11%Z; 12%Z; 21517%Z; 14%Z; 16%Z; 455%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 11: 10 <? 11 = true, msd_fuel 11 = 1, last_digit 11 = 1, so special_number_b 11 = true *)
  (* 12: 10 <? 12 = true, msd_fuel 12 = 1, last_digit 12 = 2, so special_number_b 12 = false *)
  (* 21517: 10 <? 21517 = true, msd_fuel 21517 = 2, last_digit 21517 = 7, so special_number_b 21517 = false *)
  (* 14: 10 <? 14 = true, msd_fuel 14 = 1, last_digit 14 = 4, so special_number_b 14 = false *)
  (* 16: 10 <? 16 = true, msd_fuel 16 = 1, last_digit 16 = 6, so special_number_b 16 = false *)
  (* 455: 10 <? 455 = true, msd_fuel 455 = 4, last_digit 455 = 5, so special_number_b 455 = false *)
  reflexivity.
Qed.