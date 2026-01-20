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
  specialFilter_spec [32%Z; 83%Z; 24%Z; -56%Z; 10%Z; 75%Z; 84%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 32: 10 <? 32 = true, msd_fuel 32 = 3, last_digit 32 = 2, so special_number_b 32 = false *)
  (* 83: 10 <? 83 = true, msd_fuel 83 = 8, last_digit 83 = 3, so special_number_b 83 = false *)
  (* 24: 10 <? 24 = true, msd_fuel 24 = 2, last_digit 24 = 4, so special_number_b 24 = false *)
  (* -56: 10 <? 56 = true, msd_fuel 56 = 5, last_digit 56 = 6, so special_number_b -56 = false *)
  (* 10: 10 <? 10 = false, so special_number_b 10 = false *)
  (* 75: 10 <? 75 = true, msd_fuel 75 = 7, last_digit 75 = 5, so special_number_b 75 = true *)
  (* 84: 10 <? 84 = true, msd_fuel 84 = 8, last_digit 84 = 4, so special_number_b 84 = false *)
  reflexivity.
Qed.