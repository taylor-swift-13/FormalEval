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
  specialFilter_spec [-23%Z; -15%Z; 42%Z; 99%Z; 154%Z; 42%Z; -15%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* -23: 10 <? 23 = true, msd_fuel 23 = 2, last_digit 23 = 3, so special_number_b -23 = false *)
  (* -15: 10 <? 15 = true, msd_fuel 15 = 1, last_digit 15 = 5, so special_number_b -15 = true *)
  (* 42: 10 <? 42 = true, msd_fuel 42 = 4, last_digit 42 = 2, so special_number_b 42 = false *)
  (* 99: 10 <? 99 = true, msd_fuel 99 = 9, last_digit 99 = 9, so special_number_b 99 = true *)
  (* 154: 10 <? 154 = true, msd_fuel 154 = 1, last_digit 154 = 4, so special_number_b 154 = false *)
  (* 42: 10 <? 42 = true, msd_fuel 42 = 4, last_digit 42 = 2, so special_number_b 42 = false *)
  (* -15: 10 <? 15 = true, msd_fuel 15 = 1, last_digit 15 = 5, so special_number_b -15 = true *)
  reflexivity.
Qed.