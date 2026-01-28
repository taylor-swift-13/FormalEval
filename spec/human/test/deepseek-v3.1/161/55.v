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

Example test_case_racectuuTeaaaaBFGBBccDDeear : solve_impl "racectuuTeaaaaBFGBBccDDeear"%string = "RACECTUUtEAAAAbfgbbCCddEEAR"%string.
Proof.
  unfold solve_impl.
  simpl.
  (* 计算 contains_letter_dec *)
  simpl.
  (* 展开 map change_case *)
  unfold change_case.
  (* 处理每个字符 *)
  (* 'r' - ASCII 114: is_lower_alpha = true -> my_uppercase = 114-32=82='R' *)
  simpl.
  (* 'a' - ASCII 97: is_lower_alpha = true -> my_uppercase = 97-32=65='A' *)
  simpl.
  (* 'c' - ASCII 99: is_lower_alpha = true -> my_uppercase = 99-32=67='C' *)
  simpl.
  (* 'e' - ASCII 101: is_lower_alpha = true -> my_uppercase = 101-32=69='E' *)
  simpl.
  (* 'c' - ASCII 99: is_lower_alpha = true -> my_uppercase = 99-32=67='C' *)
  simpl.
  (* 't' - ASCII 116: is_lower_alpha = true -> my_uppercase = 116-32=84='T' *)
  simpl.
  (* 'u' - ASCII 117: is_lower_alpha = true -> my_uppercase = 117-32=85='U' *)
  simpl.
  (* 'u' - ASCII 117: is_lower_alpha = true -> my_uppercase = 117-32=85='U' *)
  simpl.
  (* 'T' - ASCII 84: is_upper_alpha = true -> my_lowercase = 84+32=116='t' *)
  simpl.
  (* 'e' - ASCII 101: is_lower_alpha = true -> my_uppercase = 101-32=69='E' *)
  simpl.
  (* 'a' - ASCII 97: is_lower_alpha = true -> my_uppercase = 97-32=65='A' *)
  simpl.
  (* 'a' - ASCII 97: is_lower_alpha = true -> my_uppercase = 97-32=65='A' *)
  simpl.
  (* 'a' - ASCII 97: is_lower_alpha = true -> my_uppercase = 97-32=65='A' *)
  simpl.
  (* 'a' - ASCII 97: is_lower_alpha = true -> my_uppercase = 97-32=65='A' *)
  simpl.
  (* 'B' - ASCII 66: is_upper_alpha = true -> my_lowercase = 66+32=98='b' *)
  simpl.
  (* 'F' - ASCII 70: is_upper_alpha = true -> my_lowercase = 70+32=102='f' *)
  simpl.
  (* 'G' - ASCII 71: is_upper_alpha = true -> my_lowercase = 71+32=103='g' *)
  simpl.
  (* 'B' - ASCII 66: is_upper_alpha = true -> my_lowercase = 66+32=98='b' *)
  simpl.
  (* 'B' - ASCII 66: is_upper_alpha = true -> my_lowercase = 66+32=98='b' *)
  simpl.
  (* 'c' - ASCII 99: is_lower_alpha = true -> my_uppercase = 99-32=67='C' *)
  simpl.
  (* 'c' - ASCII 99: is_lower_alpha = true -> my_uppercase = 99-32=67='C' *)
  simpl.
  (* 'D' - ASCII 68: is_upper_alpha = true -> my_lowercase = 68+32=100='d' *)
  simpl.
  (* 'D' - ASCII 68: is_upper_alpha = true -> my_lowercase = 68+32=100='d' *)
  simpl.
  (* 'e' - ASCII 101: is_lower_alpha = true -> my_uppercase = 101-32=69='E' *)
  simpl.
  (* 'a' - ASCII 97: is_lower_alpha = true -> my_uppercase = 97-32=65='A' *)
  simpl.
  (* 'a' - ASCII 97: is_lower_alpha = true -> my_uppercase = 97-32=65='A' *)
  simpl.
  (* 'r' - ASCII 114: is_lower_alpha = true -> my_uppercase = 114-32=82='R' *)
  simpl.
  (* 最后转换为字符串 *)
  reflexivity.
Qed.