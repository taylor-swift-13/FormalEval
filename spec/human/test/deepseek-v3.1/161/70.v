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

Example new_test_case :
  solve_impl "aaaaaBBccDDeeABCDEF!!!!1234!!!!e"%string = "AAAAAbbCCddEEabcdef!!!!1234!!!!E"%string.
Proof.
  unfold solve_impl.
  simpl.
  simpl.
  unfold change_case.
  unfold change_case.
  unfold is_lower_alpha, is_upper_alpha.
  simpl.
  (* 字符 'a' - ASCII 97, 是小写字母 *)
  (* map change_case 作用：所有字母转换大小写，没有字母时反转字符 *)
  (* 'a' -> 'A' (ASCII 65) *)
  (* 'a' -> 'A' *)
  (* 'a' -> 'A' *)
  (* 'a' -> 'A' *)
  (* 'a' -> 'A' *)
  (* 'B' -> 'b' (ASCII 98) *)
  (* 'B' -> 'b' *)
  (* 'c' -> 'C' (ASCII 67) *)
  (* 'c' -> 'C' *)
  (* 'D' -> 'd' (ASCII 100) *)
  (* 'D' -> 'd' *)
  (* 'e' -> 'E' (ASCII 69) *)
  (* 'e' -> 'E' *)
  (* 'A' -> 'a' (ASCII 97) *)
  (* 'B' -> 'b' *)
  (* 'C' -> 'c' *)
  (* 'D' -> 'd' *)
  (* 'E' -> 'e' *)
  (* 字符 '!'、'1'、'2'、'3'、'4'不变 *)
  reflexivity.
Qed.