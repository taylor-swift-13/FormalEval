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
  solve_spec ["c"%char; "a"%char; "n"%char; " "%char; "y"%char; "o"%char; "u"%char; " "%char; "s"%char; "o"%char; "q"%char; "C"%char; "j"%char; "Y"%char; "u"%char; "V"%char; "c"%char; "l"%char; "v"%char; "e"%char; " "%char; "t"%char; "h"%char; "i"%char; "s"%char; " "%char; "p"%char; "r"%char; "o"%char; " "%char; "A"%char; "b"%char; "t"%char; "t"%char; "H"%char; "t"%char; "1"%char; "s"%char; " "%char; "I"%char; "s"%char; " "%char; "A"%char; " "%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "G"%char; "t"%char; "3"%char; "s"%char; "T"%char; "!"%char; "G"%char; "b"%char; "l"%char; "e"%char; "m"%char; "?"%char]
             ["C"%char; "A"%char; "N"%char; " "%char; "Y"%char; "O"%char; "U"%char; " "%char; "S"%char; "O"%char; "Q"%char; "c"%char; "J"%char; "y"%char; "U"%char; "v"%char; "C"%char; "L"%char; "V"%char; "E"%char; " "%char; "T"%char; "H"%char; "I"%char; "S"%char; " "%char; "P"%char; "R"%char; "O"%char; " "%char; "a"%char; "B"%char; "T"%char; "T"%char; "h"%char; "T"%char; "1"%char; "S"%char; " "%char; "i"%char; "S"%char; " "%char; "a"%char; " "%char; "a"%char; "b"%char; "c"%char; "d"%char; "e"%char; "f"%char; "g"%char; "T"%char; "3"%char; "S"%char; "t"%char; "!"%char; "g"%char; "B"%char; "L"%char; "E"%char; "M"%char; "?"%char].
Proof.
  unfold solve_spec.
  simpl.
  (* contains_letter_dec returns true *)
  reflexivity.
Qed.