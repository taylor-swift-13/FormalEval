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
  specialFilter_spec [101%Z; 8518%Z; 103%Z; 102%Z; 101%Z] 3%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 101: 10 <? 101 = true, msd_fuel = 1 (odd), last_digit = 1 (odd), so special_number_b 101 = true *)
  (* 8518: 10 <? 8518 = true, msd_fuel = 8 (even), so special_number_b 8518 = false *)
  (* 103: 10 <? 103 = true, msd_fuel = 1 (odd), last_digit = 3 (odd), so special_number_b 103 = true *)
  (* 102: 10 <? 102 = true, msd_fuel = 1 (odd), last_digit = 2 (even), so special_number_b 102 = false *)
  (* 101: 10 <? 101 = true, msd_fuel = 1 (odd), last_digit = 1 (odd), so special_number_b 101 = true *)
  reflexivity.
Qed.