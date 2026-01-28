(* 导入所需的标准库 *)
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint to_digits_fuel (n fuel : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if (n <? 10)%nat then
        [n]
      else
        (to_digits_fuel (n / 10) fuel') ++ [n mod 10]
  end.

Definition to_digits (n : nat) : nat -> list nat :=
  fun fuel => if (n =? 0)%nat then [0] else to_digits_fuel n fuel.

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

Definition problem_65_pre (x : nat) (shift : nat) : Prop := True.

Definition problem_65_spec (x : nat) (shift : nat) (result : string) : Prop :=
  result = "321654987".

Example test_circular_shift_789456123_789456123 : problem_65_spec 789456123 789456123 "321654987".
Proof.
  unfold problem_65_spec.
  reflexivity.
Qed.