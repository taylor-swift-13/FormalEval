Require Import Coq.Lists.List Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition last_digit (n : Z) : Z := Z.abs (n mod 10).

Fixpoint msd_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n mod 10
  | S f => if Z_lt_dec n 10 then n else msd_fuel f (n/10)
  end.

Definition special_number_b (n : Z) : bool :=
  let abs_n := Z.abs n in (10 <? n) && (Z.odd (msd_fuel (Z.to_nat abs_n) abs_n)) && (Z.odd (last_digit abs_n)).

Definition specialFilter_impl (nums : list Z) : Z := Z.of_nat (length (filter special_number_b nums)).

Definition problem_146_pre (nums : list Z) : Prop := True.

Definition problem_146_spec (nums : list Z) (output : Z) : Prop :=
  output = specialFilter_impl nums.

Example test_case : problem_146_spec [39; 153; 240; -339] 2.
Proof.
  unfold problem_146_spec, specialFilter_impl.
  simpl.
  unfold special_number_b.
  repeat (
    simpl;
    unfold last_digit;
    unfold msd_fuel;
    try (rewrite Z.odd_mod; try reflexivity)
  ).
  (* Evaluate each element step-by-step *)
  (* 39 *)
  simpl.
  unfold last_digit, msd_fuel.
  simpl.
  unfold msd_fuel.
  simpl.
  replace (39 / 10) with 3 by reflexivity.
  replace (3 <? 10) with true by reflexivity.
  simpl.
  replace (Z.odd (msd_fuel (Z.to_nat (Z.abs 39)) 39)) with true.
  2: {
    unfold msd_fuel.
    simpl.
    unfold msd_fuel.
    simpl.
    replace (Z.to_nat (Z.abs 39)) with 39%nat by reflexivity.
    simpl.
    replace (39 <? 10) with false by reflexivity.
    simpl.
    remember (msd_fuel 39 3) as v.
    rewrite Heqv.
    reflexivity.
  }
  (* 153 *)
  simpl.
  unfold last_digit, msd_fuel.
  simpl.
  unfold msd_fuel.
  simpl.
  replace (153 / 10) with 15 by reflexivity.
  replace (15 <? 10) with false by reflexivity.
  simpl.
  replace (Z.odd (msd_fuel (Z.to_nat (Z.abs 153)) 153)) with true.
  2: {
    unfold msd_fuel.
    simpl.
    unfold msd_fuel.
    simpl.
    replace (Z.to_nat (Z.abs 153)) with 153%nat by reflexivity.
    simpl.
    replace (153 <? 10) with false by reflexivity.
    simpl.
    remember (msd_fuel 153 15) as v.
    rewrite Heqv.
    reflexivity.
  }
  (* 240 *)
  simpl.
  unfold last_digit, msd_fuel.
  simpl.
  unfold msd_fuel.
  simpl.
  replace (240 / 10) with 24 by reflexivity.
  replace (24 <? 10) with false by reflexivity.
  simpl.
  replace (Z.odd (msd_fuel (Z.to_nat (Z.abs 240)) 240)) with true.
  2: {
    unfold msd_fuel.
    simpl.
    unfold msd_fuel.
    simpl.
    replace (Z.to_nat (Z.abs 240)) with 240%nat by reflexivity.
    simpl.
    replace (240 <? 10) with false by reflexivity.
    simpl.
    remember (msd_fuel 240 24) as v.
    rewrite Heqv.
    reflexivity.
  }
  (* -339 *)
  simpl.
  unfold last_digit, msd_fuel.
  simpl.
  unfold msd_fuel.
  simpl.
  replace (-339 / 10) with -33 by reflexivity.
  replace (-33 <? 10) with true by reflexivity.
  simpl.
  replace (Z.odd (msd_fuel (Z.to_nat (Z.abs (-339))) (-339))) with true.
  2: {
    unfold msd_fuel.
    simpl.
    unfold msd_fuel.
    simpl.
    replace (Z.to_nat (Z.abs (-339))) with 339%nat by reflexivity.
    simpl.
    replace (339 <? 10) with false by reflexivity.
    simpl.
    remember (msd_fuel 339  -33) as v.
    rewrite Heqv.
    reflexivity.
  }
  (* Now, count how many are true *)
  simpl.
  reflexivity.
Qed.