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
  specialFilter_spec [100%Z; 101%Z; 102%Z; 103%Z; 104%Z; 102%Z] 2%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 100: 10 <? 100 = true, msd_fuel 100 = 1, last_digit 100 = 0, so special_number_b 100 = false *)
  (* 101: 10 <? 101 = true, msd_fuel 101 = 1, last_digit 101 = 1, so special_number_b 101 = true *)
  (* 102: 10 <? 102 = true, msd_fuel 102 = 1, last_digit 102 = 2, so special_number_b 102 = false *)
  (* 103: 10 <? 103 = true, msd_fuel 103 = 1, last_digit 103 = 3, so special_number_b 103 = true *)
  (* 104: 10 <? 104 = true, msd_fuel 104 = 1, last_digit 104 = 4, so special_number_b 104 = false *)
  (* 102: 10 <? 102 = true, msd_fuel 102 = 1, last_digit 102 = 2, so special_number_b 102 = false *)
  reflexivity.
Qed.