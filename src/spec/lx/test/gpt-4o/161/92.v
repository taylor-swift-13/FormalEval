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
  solve_spec ["r"%char; "Y"%char; "a"%char; "r"%char; "r"%char; "c"%char; "a"%char; "n"%char; " "%char; "y"%char; "o"%char; "u"%char; " "%char; "s"%char; "o"%char; "l"%char; "v"%char; "e"%char; " "%char; "t"%char; "h"%char; "i"%char; "s"%char; " "%char; "p"%char; "r"%char; "o"%char; "b"%char; "l"%char; "e"%char; "m"%char; "?"%char; "a"%char; "a"%char; "Y"%char]
             ["R"%char; "y"%char; "A"%char; "R"%char; "R"%char; "C"%char; "A"%char; "N"%char; " "%char; "Y"%char; "O"%char; "U"%char; " "%char; "S"%char; "O"%char; "L"%char; "V"%char; "E"%char; " "%char; "T"%char; "H"%char; "I"%char; "S"%char; " "%char; "P"%char; "R"%char; "O"%char; "B"%char; "L"%char; "E"%char; "M"%char; "?"%char; "A"%char; "A"%char; "y"%char].
Proof.
  unfold solve_spec.
  simpl.
  reflexivity.
Qed.