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
  specialFilter_spec [-123%Z; 456%Z; 790%Z; -56%Z; 111%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* -123: 10 <? 123 = true, msd_fuel 123 = 1, last_digit 123 = 3, so special_number_b -123 = true *)
  (* 456: 10 <? 456 = true, msd_fuel 456 = 4, last_digit 456 = 6, so special_number_b 456 = false *)
  (* 790: 10 <? 790 = true, msd_fuel 790 = 7, last_digit 790 = 0, so special_number_b 790 = false *)
  (* -56: 10 <? 56 = true, msd_fuel 56 = 5, last_digit 56 = 6, so special_number_b -56 = false *)
  (* 111: 10 <? 111 = true, msd_fuel 111 = 1, last_digit 111 = 1, so special_number_b 111 = true *)
  reflexivity.
Qed.