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
  specialFilter_spec [615%Z; 4%Z; 6%Z; 5%Z; 505%Z; 12%Z; 6%Z] 1%Z.
Proof.
  unfold specialFilter_spec.
  simpl.
  (* Evaluate special_number_b for each element *)
  (* 615: 10 <? 615 = true, msd_fuel 615 = 6, last_digit 615 = 5, so special_number_b 615 = true *)
  (* 4: 10 <? 4 = false, so special_number_b 4 = false *)
  (* 6: 10 <? 6 = false, so special_number_b 6 = false *)
  (* 5: 10 <? 5 = false, so special_number_b 5 = false *)
  (* 505: 10 <? 505 = true, msd_fuel 505 = 5, last_digit 505 = 5, so special_number_b 505 = false *)
  (* 12: 10 <? 12 = true, msd_fuel 12 = 1, last_digit 12 = 2, so special_number_b 12 = false *)
  (* 6: 10 <? 6 = false, so special_number_b 6 = false *)
  reflexivity.
Qed.