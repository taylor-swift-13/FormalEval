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
  specialFilter_spec [21517%Z; 789%Z; 12%Z; 111%Z; 111%Z; 21517%Z] 3%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 21517: 10 <? 21517 = true, msd_fuel (Z.to_nat 21517) 21517 = 2 (even), last_digit 21517 = 7 (odd), so special_number_b 21517 = false *)
  (* 789: 10 <? 789 = true, msd_fuel (Z.to_nat 789) 789 = 7 (odd), last_digit 789 = 9 (odd), so special_number_b 789 = true *)
  (* 12: 10 <? 12 = true, msd_fuel (Z.to_nat 12) 12 = 1 (odd), last_digit 12 = 2 (even), so special_number_b 12 = false *)
  (* 111: 10 <? 111 = true, msd_fuel (Z.to_nat 111) 111 = 1 (odd), last_digit 111 = 1 (odd), so special_number_b 111 = true *)
  (* 111: 10 <? 111 = true, msd_fuel (Z.to_nat 111) 111 = 1 (odd), last_digit 111 = 1 (odd), so special_number_b 111 = true *)
  (* 21517: 10 <? 21517 = true, msd_fuel (Z.to_nat 21517) 21517 = 2 (even), last_digit 21517 = 7 (odd), so special_number_b 21517 = false *)
  reflexivity.
Qed.