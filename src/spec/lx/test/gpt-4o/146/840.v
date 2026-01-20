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
  specialFilter_spec [15%Z; 84%Z; -57%Z; 8518%Z; -56%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 15: 10 <? 15 = true, msd_fuel 15 = 1, last_digit 15 = 5, so special_number_b 15 = true *)
  (* 84: 10 <? 84 = true, msd_fuel 84 = 8, last_digit 84 = 4, so special_number_b 84 = false *)
  (* -57: 10 <? 57 = true, msd_fuel 57 = 5, last_digit 57 = 7, so special_number_b -57 = true *)
  (* 8518: 10 <? 8518 = true, msd_fuel 8518 = 8, last_digit 8518 = 8, so special_number_b 8518 = false *)
  (* -56: 10 <? 56 = true, msd_fuel 56 = 5, last_digit 56 = 6, so special_number_b -56 = false *)
  reflexivity.
Qed.