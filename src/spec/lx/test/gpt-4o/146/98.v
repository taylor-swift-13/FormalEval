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
  specialFilter_spec [55%Z; -62%Z; 7%Z; 24%Z; 18%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 55: 10 <? 55 = true, msd_fuel = 5, last_digit = 5, both odd, so special_number_b 55 = true *)
  (* -62: 10 <? 62 = true, msd_fuel = 6, last_digit = 2, not both odd, so special_number_b -62 = false *)
  (* 7: 10 <? 7 = false, so special_number_b 7 = false *)
  (* 24: 10 <? 24 = true, msd_fuel = 2, last_digit = 4, not both odd, so special_number_b 24 = false *)
  (* 18: 10 <? 18 = true, msd_fuel = 1, last_digit = 8, not both odd, so special_number_b 18 = false *)
  reflexivity.
Qed.