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

Example test_case_new : solve_impl " AbttHt1s Is A ABCDEFGt3sT!G"%string = " aBTThT1S iS a abcdefgT3St!g"%string.
Proof.
  unfold solve_impl.
  simpl.
  simpl.
  unfold change_case.
  simpl.
  unfold is_lower_alpha, is_upper_alpha.
  simpl.
  (* ' ' - ASCII 32: not a letter *)
  (* 'A' - ASCII 65: uppercase letter *)
  (* 'b' - ASCII 98: lowercase letter *)
  (* 't' - ASCII 116: lowercase letter *)
  (* 't' - ASCII 116 *)
  (* 'H' - ASCII 72: uppercase letter *)
  (* 't' - ASCII 116 *)
  (* '1' - ASCII 49: not a letter *)
  (* 's' - ASCII 115: lowercase letter *)
  (* ' ' *) 
  (* 'I' - ASCII 73: uppercase letter *)
  (* 's' - ASCII 115: lowercase letter *)
  (* ' ' *) 
  (* 'A' - ASCII 65: uppercase letter *)
  (* ' ' *) 
  (* 'A' - ASCII 65: uppercase letter *)
  (* ' ' *)
  (* 'A' - ASCII 65 *)
  (* 'B' - ASCII 66 *)
  (* 'C' - ASCII 67 *)
  (* 'D' - ASCII 68 *)
  (* 'E' - ASCII 69 *)
  (* 'F' - ASCII 70 *)
  (* 'G' - ASCII 71 *)
  (* 't' - ASCII 116 *)
  (* '3' - ASCII 51 *)
  (* 's' - ASCII 115 *)
  (* 'T' - ASCII 84 *)
  (* '!' - ASCII 33 *)
  (* 'G' - ASCII 71 *)

  (* Map change_case over string characters *)
  (* ' ' -> ' ' (not letter) *)
  (* 'A' -> 'a' *)
  (* 'b' -> 'B' *)
  (* 't' -> 'T' *)
  (* 't' -> 'T' *)
  (* 'H' -> 'h' *)
  (* 't' -> 'T' *)
  (* '1' -> '1' *)
  (* 's' -> 'S' *)
  (* ' ' -> ' ' *)
  (* 'I' -> 'i' *)
  (* 's' -> 'S' *)
  (* ' ' -> ' ' *)
  (* 'A' -> 'a' *)
  (* ' ' -> ' ' *)
  (* 'A' -> 'a' *)
  (* ' ' -> ' ' *)
  (* 'A' -> 'a' *)
  (* 'B' -> 'b' *)
  (* 'C' -> 'c' *)
  (* 'D' -> 'd' *)
  (* 'E' -> 'e' *)
  (* 'F' -> 'f' *)
  (* 'G' -> 'g' *)
  (* 't' -> 'T' *)
  (* '3' -> '3' *)
  (* 's' -> 'S' *)
  (* 'T' -> 't' *)
  (* '!' -> '!' *)
  (* 'G' -> 'g' *)

  (* Final string: " aBTThT1S iS a abcdefgT3St!g" *)

  reflexivity.
Qed.