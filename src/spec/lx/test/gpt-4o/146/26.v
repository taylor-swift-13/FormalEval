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
  specialFilter_spec [57%Z; -15%Z; 42%Z; 99%Z; 56%Z; 104%Z; 42%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 57: 10 <? 57 = true, msd_fuel 57 = 5, Z.odd 5 = true, last_digit 57 = 7, Z.odd 7 = true, so special_number_b 57 = true *)
  (* -15: 10 <? -15 = false, so special_number_b -15 = false *)
  (* 42: 10 <? 42 = true, msd_fuel 42 = 4, Z.odd 4 = false, so special_number_b 42 = false *)
  (* 99: 10 <? 99 = true, msd_fuel 99 = 9, Z.odd 9 = true, last_digit 99 = 9, Z.odd 9 = true, so special_number_b 99 = true *)
  (* 56: 10 <? 56 = true, msd_fuel 56 = 5, Z.odd 5 = true, last_digit 56 = 6, Z.odd 6 = false, so special_number_b 56 = false *)
  (* 104: 10 <? 104 = true, msd_fuel 104 = 1, Z.odd 1 = true, last_digit 104 = 4, Z.odd 4 = false, so special_number_b 104 = false *)
  (* 42: 10 <? 42 = true, msd_fuel 42 = 4, Z.odd 4 = false, so special_number_b 42 = false *)
  reflexivity.
Qed.