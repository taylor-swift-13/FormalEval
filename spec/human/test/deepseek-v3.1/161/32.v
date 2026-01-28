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

Example test_case_new : solve_impl "aaaaBBccDDeeABCDEF!!!!1234!!!!e"%string = "AAAAbbCCddEEabcdef!!!!1234!!!!E"%string.
Proof.
  unfold solve_impl.
  simpl.
  simpl.
  unfold change_case.
  unfold is_lower_alpha, is_upper_alpha.
  simpl.
  (* For each character, compute change_case result *)
  (* 'a' (97): lowercase -> uppercase (97-32=65='A') *)
  (* 'a' (97): lowercase -> uppercase 'A' *)
  (* 'a' (97): lowercase -> uppercase 'A' *)
  (* 'a' (97): lowercase -> uppercase 'A' *)
  (* 'B' (66): uppercase -> lowercase (66+32=98='b') *)
  (* 'B' (66): uppercase -> lowercase 'b' *)
  (* 'c' (99): lowercase -> uppercase (99-32=67='C') *)
  (* 'c' (99): lowercase -> uppercase 'C' *)
  (* 'D' (68): uppercase -> lowercase (68+32=100='d') *)
  (* 'D' (68): uppercase -> lowercase 'd' *)
  (* 'e' (101): lowercase -> uppercase (101-32=69='E') *)
  (* 'e' (101): lowercase -> uppercase 'E' *)
  (* 'A' (65): uppercase -> lowercase (65+32=97='a') *)
  (* 'B' (66): uppercase -> lowercase 'b' *)
  (* 'C' (67): uppercase -> lowercase 'c' *)
  (* 'D' (68): uppercase -> lowercase 'd' *)
  (* 'E' (69): uppercase -> lowercase 'e' *)
  (* 'F' (70): uppercase -> lowercase 'f' *)
  (* '!' (33): no change *)
  (* '!' (33): no change *)
  (* '!' (33): no change *)
  (* '!' (33): no change *)
  (* '1' (49): no change *)
  (* '2' (50): no change *)
  (* '3' (51): no change *)
  (* '4' (52): no change *)
  (* '!' (33): no change *)
  (* '!' (33): no change *)
  (* '!' (33): no change *)
  (* '!' (33): no change *)
  (* 'e' (101): lowercase -> uppercase 'E' *)
  simpl.
  reflexivity.
Qed.