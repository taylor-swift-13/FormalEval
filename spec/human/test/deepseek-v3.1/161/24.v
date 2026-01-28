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

Example test_case_custom : solve_impl "aaaaBBccDDeeABCDEFGBBccDDee"%string = "AAAAbbCCddEEabcdefgbbCCddEE"%string.
Proof.
  unfold solve_impl.
  simpl.
  (* 计算 contains_letter_dec *)
  simpl.
  (* 展开 map change_case *)
  unfold change_case.
  (* 逐字符处理 *)
  simpl.
  simpl.
  simpl.
  simpl.
  simpl.
  simpl.
  simpl.
  simpl.
  simpl.
  simpl.
  simpl.
  simpl.
  simpl.
  simpl.
  simpl.
  simpl.
  (* 现在处理每个字符对应的逻辑 *)
  (* 字符串字符ASCII值: 'a'=97, 'B'=66, 'c'=99, 'D'=68, 'e'=101, 'A'=65, 'B'=66, 'C'=67, 'D'=68, 'E'=69, 'F'=70, 'G'=71 *)
  (* 'a' - is_lower_alpha true -> my_uppercase 97-32=65='A' *)
  (* 'a' - same: 'A' *)
  (* 'a' - same: 'A' *)
  (* 'a' - same: 'A' *)
  (* 'B' - is_upper_alpha true -> my_lowercase 66+32=98='b' *)
  (* 'B' - same: 'b' *)
  (* 'c' - is_lower_alpha true -> my_uppercase 99-32=67='C' *)
  (* 'c' - same: 'C' *)
  (* 'c' - same: 'C' *)
  (* 'D' - is_upper_alpha true -> my_lowercase 68+32=100='d' *)
  (* 'D' - same: 'd' *)
  (* 'e' - is_lower_alpha true -> my_uppercase 101-32=69='E' *)
  (* 'e' - same: 'E' *)
  (* 'e' - same: 'E' *)
  (* 'A' - is_upper_alpha true -> my_lowercase 65+32=97='a' *)
  (* 'B' - same as above: 'b' *)
  (* 'C' - same as above: 'c' *)
  (* 'D' - same as above: 'd' *)
  (* 'E' - same as above: 'e' *)
  (* 'F' - same as above: 'f' *)
  (* 'G' - same as above: 'g' *)
  (* 'B' - same as above: 'b' *)
  (* 'B' - same as above: 'b' *)
  (* 'c' - as above: 'C' -> 'C' and then to 'c' or 'C'? Wait, 'c' is lowercase, so change to uppercase -> 'C' and 'D'-> 'd' -> 'D' *)
  (* Wait, check carefully: *)
  (* For each character, as above, they are converted accordingly. *)
  (* The final string should be: *)
  (* "AAAAbbCCddEEabcdefgbbCCddEE" *)
  reflexivity.
Qed.