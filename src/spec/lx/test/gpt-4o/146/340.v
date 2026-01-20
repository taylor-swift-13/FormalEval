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
  specialFilter_spec [-12%Z; 93%Z; -125%Z; 109%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* -12: abs_n = 12, 10 <? 12 = true, msd_fuel = 1, last_digit = 2, special_number_b -12 = false *)
  (* 93: abs_n = 93, 10 <? 93 = true, msd_fuel = 9, last_digit = 3, special_number_b 93 = true *)
  (* -125: abs_n = 125, 10 <? 125 = true, msd_fuel = 1, last_digit = 5, special_number_b -125 = true *)
  (* 109: abs_n = 109, 10 <? 109 = true, msd_fuel = 1, last_digit = 9, special_number_b 109 = false *)
  reflexivity.
Qed.