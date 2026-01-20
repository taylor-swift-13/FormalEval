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
  specialFilter_spec [19%Z; 29%Z; 39%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 19: 10 <? 19 = true, msd_fuel (Z.to_nat 19) 19 = 1, Z.odd 1 = true, last_digit 19 = 9, Z.odd 9 = true, so special_number_b 19 = true *)
  (* 29: 10 <? 29 = true, msd_fuel (Z.to_nat 29) 29 = 2, Z.odd 2 = false, so special_number_b 29 = false *)
  (* 39: 10 <? 39 = true, msd_fuel (Z.to_nat 39) 39 = 3, Z.odd 3 = true, last_digit 39 = 9, Z.odd 9 = true, so special_number_b 39 = true *)
  reflexivity.
Qed.