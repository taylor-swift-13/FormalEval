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
  specialFilter_spec [102%Z; 8518%Z; 103%Z; 104%Z; 102%Z; 918%Z; 8518%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 102: 10 <? 102 = true, msd_fuel 102 = 1, last_digit 102 = 2, special_number_b 102 = false *)
  (* 8518: 10 <? 8518 = true, msd_fuel 8518 = 8, last_digit 8518 = 8, special_number_b 8518 = false *)
  (* 103: 10 <? 103 = true, msd_fuel 103 = 1, last_digit 103 = 3, special_number_b 103 = true *)
  (* 104: 10 <? 104 = true, msd_fuel 104 = 1, last_digit 104 = 4, special_number_b 104 = false *)
  (* 102: 10 <? 102 = true, msd_fuel 102 = 1, last_digit 102 = 2, special_number_b 102 = false *)
  (* 918: 10 <? 918 = true, msd_fuel 918 = 9, last_digit 918 = 8, special_number_b 918 = false *)
  (* 8518: 10 <? 8518 = true, msd_fuel 8518 = 8, last_digit 8518 = 8, special_number_b 8518 = false *)
  reflexivity.
Qed.