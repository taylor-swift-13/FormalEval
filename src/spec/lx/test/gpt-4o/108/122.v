Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

Import ListNotations.

Fixpoint nat_sum_digits_aux (n : nat) (fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match n with
    | 0 => 0
    | _ => (n mod 10) + nat_sum_digits_aux (n / 10) fuel'
    end
  end.

Fixpoint nat_get_msd_aux (n : nat) (fuel : nat) : nat :=
  match fuel with
  | 0 => n
  | S fuel' =>
    if (n <? 10)%nat then n
    else nat_get_msd_aux (n / 10) fuel'
  end.

Definition nat_sum_digits (n : nat) : nat :=
  nat_sum_digits_aux n n.

Definition nat_get_msd (n : nat) : nat :=
  nat_get_msd_aux n n.

Definition sum_digits (n : Z) : Z :=
  if Z_gt_dec n 0 then
    Z.of_nat (nat_sum_digits (Z.to_nat n))
  else if Z.eq_dec n 0 then
    0
  else
    let p_nat := Z.to_nat (-n) in
    let total_sum := Z.of_nat (nat_sum_digits p_nat) in
    let msd := Z.of_nat (nat_get_msd p_nat) in
    total_sum - 2 * msd.

Definition count_nums_spec (l : list Z) (count : nat) : Prop :=
  count = length (filter (fun z => Z.gtb (sum_digits z) 0) l).

Example count_nums_test_case :
  count_nums_spec [0%Z; 0%Z; 30%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 99%Z; 0%Z] 2.
Proof.
  unfold count_nums_spec.
  simpl.
  reflexivity.
Qed.