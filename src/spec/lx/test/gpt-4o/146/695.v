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
  specialFilter_spec [33%Z; 1110%Z; 7113%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 33: 10 <? 33 = true, msd_fuel (Z.to_nat 33) 33 = 3 (odd), last_digit 33 = 3 (odd), so special_number_b 33 = true *)
  (* 1110: 10 <? 1110 = true, msd_fuel (Z.to_nat 1110) 1110 = 1 (odd), last_digit 1110 = 0 (even), so special_number_b 1110 = false *)
  (* 7113: 10 <? 7113 = true, msd_fuel (Z.to_nat 7113) 7113 = 7 (odd), last_digit 7113 = 3 (odd), so special_number_b 7113 = true *)
  reflexivity.
Qed.