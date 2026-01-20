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

Example specialFilter_impl_ex: specialFilter_impl (15%Z :: (-73)%Z :: 14%Z :: (-15)%Z :: nil) = 1%Z.
Proof. reflexivity. Qed.

Example specialFilter_impl_ex2:
  specialFilter_impl (33%Z :: (-2)%Z :: (-3)%Z :: 45%Z :: 21%Z :: 109%Z :: nil) = 2%Z.
Proof. reflexivity. Qed.

Definition specialFilter_spec (nums : list Z) (output : Z) : Prop :=
  output = specialFilter_impl nums.
