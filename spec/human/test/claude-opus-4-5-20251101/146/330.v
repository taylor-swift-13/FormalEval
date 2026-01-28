Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.Ascii.
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

Example test_specialFilter_2 : problem_146_spec [789%Z; 93%Z; -125%Z; 121%Z; 109%Z; 111%Z; -125%Z; 11%Z] 6%Z.
Proof.
  unfold problem_146_spec.
  unfold specialFilter_impl.
  simpl.
  reflexivity.
Qed.