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
  solve_spec ["!"%char; "!"%char; "!"%char; "!"%char; "1"%char; "a"%char; "a"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "G"%char; "B"%char; "B"%char; "c"%char; "c"%char; "D"%char; "D"%char; "e"%char; "e"%char; "2"%char; "3"%char; "4"%char; "!"%char; "!"%char; "!"%char; "a"%char; "a"%char; "a"%char; "a"%char; "B"%char; "B"%char; "c"%char; "c"%char; "D"%char; "D"%char; "e"%char; "e"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "!"%char; "!"%char; "!"%char; "!"%char; "1"%char; "2"%char; "3"%char; "4"%char; "!"%char; "!"%char; "!"%char; "e"%char; "!"%char]
             ["!"%char; "!"%char; "!"%char; "!"%char; "1"%char; "A"%char; "A"%char; "a"%char; "b"%char; "c"%char; "d"%char; "e"%char; "f"%char; "g"%char; "b"%char; "b"%char; "C"%char; "C"%char; "d"%char; "d"%char; "E"%char; "E"%char; "2"%char; "3"%char; "4"%char; "!"%char; "!"%char; "!"%char; "A"%char; "A"%char; "A"%char; "A"%char; "b"%char; "b"%char; "C"%char; "C"%char; "d"%char; "d"%char; "E"%char; "E"%char; "a"%char; "b"%char; "c"%char; "d"%char; "e"%char; "f"%char; "!"%char; "!"%char; "!"%char; "!"%char; "1"%char; "2"%char; "3"%char; "4"%char; "!"%char; "!"%char; "!"%char; "E"%char; "!"%char].
Proof.
  unfold solve_spec.
  simpl.
  (* contains_letter_dec returns true *)
  reflexivity.
Qed.