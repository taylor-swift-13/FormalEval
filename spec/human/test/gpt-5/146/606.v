Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.Ascii Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

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

Example problem_146_example_spec :
  problem_146_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 21%Z; 22%Z; 23%Z; 24%Z; 25%Z; 26%Z; 27%Z; 28%Z; 29%Z; 50%Z; 51%Z; 52%Z; 53%Z; 54%Z; 55%Z; 56%Z; 57%Z; 58%Z; 59%Z; 91%Z; 92%Z; 93%Z; 94%Z; 95%Z; 96%Z; 97%Z; 98%Z; 99%Z] 15%Z.
Proof.
  unfold problem_146_spec.
  vm_compute.
  reflexivity.
Qed.