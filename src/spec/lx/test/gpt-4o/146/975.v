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
  specialFilter_spec [31%Z; 84%Z; 75%Z; -56%Z; 64%Z; 74%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 31: 10 <? 31 = true, msd_fuel 31 = 3, last_digit 31 = 1, Z.odd 3 = true, Z.odd 1 = true, so special_number_b 31 = true *)
  (* 84: 10 <? 84 = true, msd_fuel 84 = 8, last_digit 84 = 4, Z.odd 8 = false, so special_number_b 84 = false *)
  (* 75: 10 <? 75 = true, msd_fuel 75 = 7, last_digit 75 = 5, Z.odd 7 = true, Z.odd 5 = true, so special_number_b 75 = true *)
  (* -56: 10 <? -56 = false, so special_number_b -56 = false *)
  (* 64: 10 <? 64 = true, msd_fuel 64 = 6, last_digit 64 = 4, Z.odd 6 = false, so special_number_b 64 = false *)
  (* 74: 10 <? 74 = true, msd_fuel 74 = 7, last_digit 74 = 4, Z.odd 7 = true, Z.odd 4 = false, so special_number_b 74 = false *)
  reflexivity.
Qed.