Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.Init.Nat.
Import ListNotations.

Fixpoint nat_sum_digits_aux (n : nat) (fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' => match n with 0 => 0 | _ => (n mod 10) + nat_sum_digits_aux (n / 10) fuel' end
  end.
Fixpoint nat_get_msd_aux (m : nat) (fuel : nat) : nat :=
  match fuel with
  | 0 => m
  | S fuel' => if m <? 10 then m else nat_get_msd_aux (m / 10) fuel'
  end.

Definition nat_sum_digits (n : nat) : nat := nat_sum_digits_aux n n.
Definition nat_get_msd (n : nat) : nat := nat_get_msd_aux n n.

Definition sum_digits (z : Z) : Z :=
  if Z_gt_dec z 0 then Z.of_nat (nat_sum_digits (Z.to_nat z))
  else if Z.eq_dec z 0 then 0%Z
  else let p := Z.to_nat (Z.opp z) in Z.of_nat (nat_sum_digits p) - (2%Z) * (Z.of_nat (nat_get_msd p)).

Definition count_nums_impl (l : list Z) : nat :=
  length (filter (fun z => Z.gtb (sum_digits z) 0%Z) l).

Definition problem_108_pre (l : list Z) : Prop := True.

Definition problem_108_spec (l : list Z) (output : nat) : Prop :=
  output = count_nums_impl l.

Example problem_108_test_case_mixed_spec :
  problem_108_spec (concat ([[101%Z; (Z.opp 202%Z); 303%Z; (Z.opp 404%Z); 505%Z; (Z.opp 606%Z)]] : list (list Z))) 3%nat.
Proof.
  unfold problem_108_spec, count_nums_impl.
  vm_compute.
  reflexivity.
Qed.

Example problem_108_test_case_mixed_Z :
  Z.of_nat (count_nums_impl (concat ([[101%Z; (Z.opp 202%Z); 303%Z; (Z.opp 404%Z); 505%Z; (Z.opp 606%Z)]] : list (list Z)))) = 3%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.