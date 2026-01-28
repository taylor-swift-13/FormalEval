Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

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

Example test_case_new : solve_impl "tH1s Is A t3sT!"%string = "Th1S iS a T3St!"%string.
Proof.
  unfold solve_impl.
  simpl.
  simpl.
  unfold change_case.
  unfold is_lower_alpha, is_upper_alpha.
  simpl.
  unfold my_uppercase, my_lowercase.
  simpl.
  simpl.
  (* 't' - ASCII 116: is_lower_alpha = true -> my_uppercase = 116-32=84='T' *)
  (* 'H' - ASCII 72: is_upper_alpha = true -> my_lowercase = 72+32=104='h' *)
  (* '1' - ASCII 49: not letter -> unchanged *)
  (* 's' - ASCII 115: is_lower_alpha = true -> my_uppercase=115-32=83='S' *)
  (* ' ' - ASCII 32: no change *)
  (* 'I' - ASCII 73: is_upper_alpha = true -> my_lowercase=73+32=105='i' *)
  (* 's' - ASCII 115: is_lower_alpha = true -> my_uppercase=115-32=83='S' *)
  (* ' ' - ASCII 32: no change *)
  (* 'A' - ASCII 65: is_upper_alpha = true -> my_lowercase=65+32=97='a' *)
  (* ' ' - ASCII 32: no change *)
  (* 't' - ASCII 116: is_lower_alpha = true -> my_uppercase=116-32=84='T' *)
  (* '3' - ASCII 51: no change *)
  (* 's' - ASCII 115: is_lower_alpha = true -> my_uppercase=115-32=83='S' *)
  (* 'T' - ASCII 84: is_upper_alpha = true -> my_lowercase=84+32=116='t' *)
  (* '!' - ASCII 33: no change *)
  simpl.
  reflexivity.
Qed.