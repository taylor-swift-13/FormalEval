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

Example test_case_AsDf : solve_impl "AsDf"%string = "aSdF"%string.
Proof.
  unfold solve_impl.
  simpl.
  (* 计算 contains_letter_dec *)
  simpl.
  (* 展开 map change_case *)
  unfold change_case.
  (* 处理每个字符 *)
  (* 'A' - ASCII 65: is_upper_alpha = true -> my_lowercase = 65+32=97='a' *)
  simpl.
  (* 's' - ASCII 115: is_lower_alpha = true -> my_uppercase = 115-32=83='S' *)
  simpl. 
  (* 'D' - ASCII 68: is_upper_alpha = true -> my_lowercase = 68+32=100='d' *)
  simpl.
  (* 'f' - ASCII 102: is_lower_alpha = true -> my_uppercase = 102-32=70='F' *)
  simpl.
  (* 展开 my_uppercase 和 my_lowercase *)
  unfold my_uppercase, my_lowercase.
  (* 展开 is_lower_alpha 和 is_upper_alpha *)
  unfold is_lower_alpha, is_upper_alpha.
  (* 计算布尔表达式和算术运算 *)
  simpl.
  (* 转换为字符串 *)
  reflexivity.
Qed.