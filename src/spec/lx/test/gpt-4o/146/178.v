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
  specialFilter_spec [455%Z; 123%Z; 789%Z; 111%Z; 21518%Z; 789%Z] 4%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 455: 10 <? 455 = true, msd_fuel 455 = 4, last_digit 455 = 5, so special_number_b 455 = false *)
  (* 123: 10 <? 123 = true, msd_fuel 123 = 1, last_digit 123 = 3, so special_number_b 123 = true *)
  (* 789: 10 <? 789 = true, msd_fuel 789 = 7, last_digit 789 = 9, so special_number_b 789 = true *)
  (* 111: 10 <? 111 = true, msd_fuel 111 = 1, last_digit 111 = 1, so special_number_b 111 = true *)
  (* 21518: 10 <? 21518 = true, msd_fuel 21518 = 2, last_digit 21518 = 8, so special_number_b 21518 = false *)
  (* 789: 10 <? 789 = true, msd_fuel 789 = 7, last_digit 789 = 9, so special_number_b 789 = true *)
  reflexivity.
Qed.