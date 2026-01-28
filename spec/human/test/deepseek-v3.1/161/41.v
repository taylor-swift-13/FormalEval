Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

(* 辅助定义 *)
Definition is_lower_alpha (a : ascii) : bool :=
  (("a"%char <=? a)%char && (a <=? "z"%char)%char).

Definition is_upper_alpha (a : ascii) : bool :=
  (("A"%char <=? a)%char && (a <=? "Z"%char)%char).

Definition is_letter_dec (a : ascii) : bool :=
  is_lower_alpha a || is_upper_alpha a.

Definition my_uppercase (a : ascii) : ascii :=
  if is_lower_alpha a
  then ascii_of_nat (nat_of_ascii a - 32)
  else a.

Definition my_lowercase (a : ascii) : ascii :=
  if is_upper_alpha a
  then ascii_of_nat (nat_of_ascii a + 32)
  else a.

Definition change_case (a : ascii) : ascii :=
  if is_lower_alpha a then
    my_uppercase a
  else if is_upper_alpha a then
    my_lowercase a
  else
    a.

Fixpoint contains_letter_dec (s : list ascii) : bool :=
  match s with
  | [] => false
  | h :: t => is_letter_dec h || contains_letter_dec t
  end.

Definition solve_impl (s : string) : string :=
  let l := list_ascii_of_string s in
  if contains_letter_dec l
  then string_of_list_ascii (map change_case l)
  else string_of_list_ascii (rev l).

Example test_case_qCjYuVc : solve_impl "qCjYuVc"%string = "QcJyUvC"%string.
Proof.
  unfold solve_impl.
  simpl.
  simpl.
  unfold change_case.
  unfold is_lower_alpha, is_upper_alpha.
  simpl.
  unfold my_uppercase, my_lowercase.
  simpl.
  (* 'q' - ASCII 113: is_lower_alpha = true -> my_uppercase = 113 - 32 = 81='Q' *)
  (* 'C' - ASCII 67: is_upper_alpha = true -> my_lowercase = 67 + 32 = 99='c' *)
  (* 'j' - ASCII 106: is_lower_alpha = true -> my_uppercase = 106 - 32 = 74='J' *)
  (* 'Y' - ASCII 89: is_upper_alpha = true -> my_lowercase = 89 + 32 = 121='y' *)
  (* 'u' - ASCII 117: is_lower_alpha = true -> my_uppercase = 117 - 32 = 85='U' *)
  (* 'V' - ASCII 86: is_upper_alpha = true -> my_lowercase = 86 + 32 = 118='v' *)
  (* 'c' - ASCII 99: is_lower_alpha = true -> my_uppercase = 99 - 32 = 67='C' *)
  simpl.
  reflexivity.
Qed.