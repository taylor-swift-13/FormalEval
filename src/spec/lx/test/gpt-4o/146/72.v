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
  specialFilter_spec [239%Z; 39%Z; 152%Z; 39%Z; 240%Z; -339%Z; -339%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 239: 10 <? 239 = true, msd_fuel (Z.to_nat 239) 239 = 2, last_digit 239 = 9, special_number_b 239 = false *)
  (* 39: 10 <? 39 = true, msd_fuel (Z.to_nat 39) 39 = 3, last_digit 39 = 9, special_number_b 39 = true *)
  (* 152: 10 <? 152 = true, msd_fuel (Z.to_nat 152) 152 = 1, last_digit 152 = 2, special_number_b 152 = false *)
  (* 39: 10 <? 39 = true, msd_fuel (Z.to_nat 39) 39 = 3, last_digit 39 = 9, special_number_b 39 = true *)
  (* 240: 10 <? 240 = true, msd_fuel (Z.to_nat 240) 240 = 2, last_digit 240 = 0, special_number_b 240 = false *)
  (* -339: 10 <? -339 = false, special_number_b -339 = false *)
  (* -339: 10 <? -339 = false, special_number_b -339 = false *)
  reflexivity.
Qed.