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
  specialFilter_spec [-123%Z; 456%Z; 112%Z; 1111%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* -123: abs(-123) = 123, 10 <? 123 = true, msd_fuel 123 123 = 1, odd 1 = true, last_digit 123 = 3, odd 3 = true, so special_number_b -123 = true *)
  (* 456: 10 <? 456 = true, msd_fuel 456 456 = 4, odd 4 = false, so special_number_b 456 = false *)
  (* 112: 10 <? 112 = true, msd_fuel 112 112 = 1, odd 1 = true, last_digit 112 = 2, odd 2 = false, so special_number_b 112 = false *)
  (* 1111: 10 <? 1111 = true, msd_fuel 1111 1111 = 1, odd 1 = true, last_digit 1111 = 1, odd 1 = true, so special_number_b 1111 = true *)
  reflexivity.
Qed.