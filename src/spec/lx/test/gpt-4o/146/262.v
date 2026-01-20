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
  specialFilter_spec [-2%Z; 1111%Z; 4%Z; 6%Z; 8%Z; 10%Z; 12%Z; 15%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* -2: 10 <? 2 = false, so special_number_b -2 = false *)
  (* 1111: 10 <? 1111 = true, msd_fuel (Z.to_nat 1111) 1111 = 1, last_digit 1111 = 1, both odd, so special_number_b 1111 = true *)
  (* 4: 10 <? 4 = false, so special_number_b 4 = false *)
  (* 6: 10 <? 6 = false, so special_number_b 6 = false *)
  (* 8: 10 <? 8 = false, so special_number_b 8 = false *)
  (* 10: 10 <? 10 = false, so special_number_b 10 = false *)
  (* 12: 10 <? 12 = true, msd_fuel (Z.to_nat 12) 12 = 1, last_digit 12 = 2, not both odd, so special_number_b 12 = false *)
  (* 15: 10 <? 15 = true, msd_fuel (Z.to_nat 15) 15 = 1, last_digit 15 = 5, both odd, so special_number_b 15 = true *)
  reflexivity.
Qed.