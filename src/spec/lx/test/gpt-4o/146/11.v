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
  specialFilter_spec [101%Z; -35%Z; 16%Z; 44%Z; -67%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 101: 10 <? 101 = true, msd_fuel (Z.to_nat 101) 101 = 1, last_digit 101 = 1, so special_number_b 101 = true *)
  (* -35: 10 <? -35 = false, so special_number_b -35 = false *)
  (* 16: 10 <? 16 = true, msd_fuel (Z.to_nat 16) 16 = 1, last_digit 16 = 6, so special_number_b 16 = false *)
  (* 44: 10 <? 44 = true, msd_fuel (Z.to_nat 44) 44 = 4, last_digit 44 = 4, so special_number_b 44 = false *)
  (* -67: 10 <? -67 = false, so special_number_b -67 = false *)
  reflexivity.
Qed.