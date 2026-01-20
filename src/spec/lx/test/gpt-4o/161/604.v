(* Required imports *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* Definition of is_lower_alpha *)
Definition is_lower_alpha (a : ascii) : bool :=
  (("a"%char <=? a)%char && (a <=? "z"%char)%char).

(* Definition of is_upper_alpha *)
Definition is_upper_alpha (a : ascii) : bool :=
  (("A"%char <=? a)%char && (a <=? "Z"%char)%char).

(* Definition of is_letter_dec *)
Definition is_letter_dec (a : ascii) : bool :=
  is_lower_alpha a || is_upper_alpha a.

(* Definition of my_uppercase *)
Definition my_uppercase (a : ascii) : ascii :=
  if is_lower_alpha a
  then ascii_of_nat (nat_of_ascii a - 32)
  else a.

(* Definition of my_lowercase *)
Definition my_lowercase (a : ascii) : ascii :=
  if is_upper_alpha a
  then ascii_of_nat (nat_of_ascii a + 32)
  else a.

(* Definition of change_case *)
Definition change_case (a : ascii) : ascii :=
  if is_lower_alpha a then
    my_uppercase a
  else if is_upper_alpha a then
    my_lowercase a
  else
    a.

(* Definition of contains_letter_dec *)
Fixpoint contains_letter_dec (s : list ascii) : bool :=
  match s with
  | [] => false
  | h :: t => is_letter_dec h || contains_letter_dec t
  end.

(* Specification of solve *)
Definition solve_spec (s s' : list ascii) : Prop :=
  if contains_letter_dec s
  then s' = map change_case s
  else s' = rev s.

(* Test case *)
Example solve_test :
  solve_spec ["!"%char; "W"%char; "I"%char; "T"%char; "H"%char; " "%char; "S"%char; "P"%char; "E"%char; "C"%char; "I"%char; "A"%char; "L"%char; " "%char; "C"%char; "H"%char; "A"%char; "R"%char; "A"%char; "C"%char; "T"%char; "E"%char; "R"%char; "S"%char; "!"%char; "!"%char]
             ["!"%char; "w"%char; "i"%char; "t"%char; "h"%char; " "%char; "s"%char; "p"%char; "e"%char; "c"%char; "i"%char; "a"%char; "l"%char; " "%char; "c"%char; "h"%char; "a"%char; "r"%char; "a"%char; "c"%char; "t"%char; "e"%char; "r"%char; "s"%char; "!"%char; "!"%char].
Proof.
  unfold solve_spec.
  simpl.
  (* contains_letter_dec returns true *)
  reflexivity.
Qed.