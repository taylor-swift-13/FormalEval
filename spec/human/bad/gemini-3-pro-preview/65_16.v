Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.

(* Provided Definitions *)

Fixpoint to_digits_fuel (n fuel : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if (n <? 10)%nat then
        [n]
      else
        (to_digits_fuel (n / 10) fuel') ++ [n mod 10]
  end.

Definition to_digits (n : nat) : list nat :=
  if (n =? 0)%nat then
    [0]
  else
    to_digits_fuel n n.

Definition digit_to_string (d : nat) : string :=
  match d with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | _ => ""
  end.

Fixpoint from_digits_to_string (l : list nat) : string :=
  match l with
  | [] => ""
  | h :: t => (digit_to_string h) ++ (from_digits_to_string t)
  end.

Definition circular_shift_impl (x : nat) (shift : nat) : string :=
  let digits := to_digits x in
  let len := length digits in
  if (x =? 0)%nat then
    "0"
  else
    if (len <? shift)%nat then
      from_digits_to_string (rev digits)
    else
      let effective_shift := shift mod len in
      if (effective_shift =? 0)%nat then
        from_digits_to_string digits
      else
        let split_point := len - effective_shift in
        let new_head := skipn split_point digits in
        let new_tail := firstn split_point digits in
        from_digits_to_string (new_head ++ new_tail).

Definition problem_65_pre (x : nat) (shift : nat) : Prop := True.

Definition problem_65_spec (x : nat) (shift : nat) (result : string) : Prop :=
  result = circular_shift_impl x shift.

(* Test Case Proof *)

Example test_circular_shift_23_789456124 : problem_65_spec 23 (Z.to_nat 789456124%Z) "32".
Proof.
  unfold problem_65_spec, circular_shift_impl.
  replace (to_digits 23) with [2; 3] by (vm_compute; reflexivity).
  simpl length.
  assert (H: (2 <? Z.to_nat 789456124%Z)%nat = true).
  {
    apply Nat.ltb_lt.
    replace 2 with (Z.to_nat 2%Z) by (vm_compute; reflexivity).
    apply Z2Nat.inj_lt.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
  }
  rewrite H.
  vm_compute.
  reflexivity.
Qed.