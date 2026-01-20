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
  specialFilter_spec [-124%Z; 789%Z; 615%Z; 14%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* -124: 10 <? 124 = true, msd_fuel 124 = 1 (odd), last_digit 124 = 4 (even), so special_number_b -124 = false *)
  (* 789: 10 <? 789 = true, msd_fuel 789 = 7 (odd), last_digit 789 = 9 (odd), so special_number_b 789 = true *)
  (* 615: 10 <? 615 = true, msd_fuel 615 = 6 (even), last_digit 615 = 5 (odd), so special_number_b 615 = false *)
  (* 14: 10 <? 14 = true, msd_fuel 14 = 1 (odd), last_digit 14 = 4 (even), so special_number_b 14 = false *)
  reflexivity.
Qed.