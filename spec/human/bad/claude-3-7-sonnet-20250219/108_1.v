Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.Init.Nat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint nat_sum_digits_aux (n : nat) (fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match n with
    | 0 => 0
    | _ => (n mod 10) + nat_sum_digits_aux (n / 10) fuel'
    end
  end.

Fixpoint nat_get_msd_aux (m : nat) (fuel : nat) : nat :=
  match fuel with
  | 0 => m
  | S fuel' =>
    if m <? 10 then m else nat_get_msd_aux (m / 10) fuel'
  end.

Definition nat_sum_digits (n : nat) : nat := nat_sum_digits_aux n n.

Definition nat_get_msd (n : nat) : nat := nat_get_msd_aux n n.

Definition sum_digits (z : Z) : Z :=
  if Z_gt_dec z 0 then
    Z.of_nat (nat_sum_digits (Z.to_nat z))
  else if Z.eq_dec z 0 then
    0%Z
  else
    let p := Z.to_nat (- z) in
    Z.of_nat (nat_sum_digits p) - 2 * (Z.of_nat (nat_get_msd p)).

Definition count_nums_impl (l : list Z) : nat :=
  length (filter (fun z => Z.gtb (sum_digits z) 0%Z) l).

Definition problem_108_pre (l : list Z) : Prop := True.

Definition problem_108_spec (l : list Z) (output : nat) : Prop :=
  output = count_nums_impl l.

Example test_empty_list :
  problem_108_spec [] 0.
Proof.
  unfold problem_108_spec, count_nums_impl.
  simpl.
  reflexivity.
Qed.

Example test_example_1 :
  problem_108_spec [-1; 11; -11] 1.
Proof.
  unfold problem_108_spec, count_nums_impl.
  simpl.

  (* Let's evaluate sum_digits for -1, 11, -11 to check which are >0 *)
  (* sum_digits (-1) = nat_sum_digits 1 - 2 * nat_get_msd 1 *)
  (* nat_sum_digits 1 = 1, nat_get_msd 1 = 1, so sum_digits(-1) = 1 - 2*1 = -1 < 0 *)
  (* sum_digits (11) = nat_sum_digits 11 *)
  (* nat_sum_digits 11 = 1 + 1 = 2 > 0 *)
  (* sum_digits (-11) = nat_sum_digits 11 - 2 * nat_get_msd 11 *)
  (* nat_sum_digits 11 = 2; nat_get_msd 11 = 1; sum_digits(-11) = 2 - 2*1 = 0 (not >0) *)

  (* So only one number (11) has sum_digits > 0 *)

  reflexivity.
Qed.

Example test_example_2 :
  problem_108_spec [1; 1; 2] 3.
Proof.
  unfold problem_108_spec, count_nums_impl.
  simpl.
  
  (* sum_digits of each positive number equals sum of digits *)
  (* 1 -> sum_digits = 1 > 0 *)
  (* 1 -> 1 > 0 *)
  (* 2 -> 2 > 0 *)
  (* All three > 0 -> count = 3 *)
  
  reflexivity.
Qed.