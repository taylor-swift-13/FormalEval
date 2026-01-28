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

Example test_case_Y_arrray : solve_impl "Y!!!!!1234!!!3!arraY"%string = "y!!!!!1234!!!3!ARRAy"%string.
Proof.
  unfold solve_impl.
  simpl.
  simpl.
  unfold change_case.
  unfold is_lower_alpha, is_upper_alpha.
  simpl.
  (* 'Y' - ASCII 89: is_upper_alpha = true -> my_lowercase = 89+32=121='y' *)
  (* '!' - ASCII 33: not alpha *)
  (* '1' - ASCII 49: not alpha *)
  (* '2' - ASCII 50: not alpha *)
  (* '3' - ASCII 51: not alpha *)
  (* '4' - ASCII 52: not alpha *)
  (* '!' - ASCII 33: not alpha *)
  (* '!' - ASCII 33: not alpha *)
  (* '!' - ASCII 33: not alpha *)
  (* '3' - ASCII 51: not alpha *)
  (* '!' - ASCII 33: not alpha *)
  (* 'a' - ASCII 97: is_lower_alpha = true -> my_uppercase = 97-32=65='A' *)
  (* 'r' - ASCII 114: is_lower_alpha = true -> my_uppercase=114-32=82='R' *)
  (* 'r' - ASCII 114 *)
  (* 'a' - ASCII 97 *)
  (* 'Y' - ASCII 89: is_upper_alpha = true -> my_lowercase=89+32=121='y' *)
  unfold change_case.
  repeat rewrite is_lower_alpha.
  repeat rewrite is_upper_alpha.
  simpl.
  reflexivity.
Qed.