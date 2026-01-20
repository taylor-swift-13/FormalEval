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
  specialFilter_spec [110%Z; -123%Z; 456%Z; 788%Z; 111%Z; -123%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 110: 10 <? 110 = true, msd_fuel = 1, last_digit = 0, so special_number_b 110 = false *)
  (* -123: 10 <? -123 = false, so special_number_b -123 = false *)
  (* 456: 10 <? 456 = true, msd_fuel = 4, last_digit = 6, so special_number_b 456 = false *)
  (* 788: 10 <? 788 = true, msd_fuel = 7, last_digit = 8, so special_number_b 788 = false *)
  (* 111: 10 <? 111 = true, msd_fuel = 1, last_digit = 1, so special_number_b 111 = true *)
  (* -123: 10 <? -123 = false, so special_number_b -123 = false *)
  reflexivity.
Qed.