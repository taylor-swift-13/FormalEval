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
  specialFilter_spec [-324%Z; 119%Z; 456%Z; 120%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* -324: 10 <? -324 = false, so special_number_b -324 = false *)
  (* 119: 10 <? 119 = true, msd_fuel (Z.to_nat 119) 119 = 1 (odd), last_digit 119 = 9 (odd), so special_number_b 119 = true *)
  (* 456: 10 <? 456 = true, msd_fuel (Z.to_nat 456) 456 = 4 (even), so special_number_b 456 = false *)
  (* 120: 10 <? 120 = true, msd_fuel (Z.to_nat 120) 120 = 1 (odd), last_digit 120 = 0 (even), so special_number_b 120 = false *)
  reflexivity.
Qed.