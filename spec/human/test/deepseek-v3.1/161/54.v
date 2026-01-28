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

Example test_case_new : solve_impl "!!!!1aaABCDEFGBBccDDee234!!!aaaaBBccDDeeABCDEF!!!!1234!!e!"%string = "!!!!1AAabcdefgbbCCddEE234!!!AAAAbbCCddEEabcdef!!!!1234!!E!"%string.
Proof.
  unfold solve_impl.
  simpl.
  (* 计算 contains_letter_dec *)
  simpl.
  (* 展开 map change_case *)
  unfold change_case.
  (* 处理每个字符 *)
  (* 由于具体字符较多，下面通过逐步计算验证 *)
  (* '!' - ASCII 33: not letter, remains same *)
  (* '!' ... remains same *)
  (* '1' ... remains same *)
  (* 'a' (97): is_lower_alpha = true -> uppercase 'A' (65) *)
  (* 'a' (97): uppercase -> 'A' (65) *)
  (* 'A' (65): uppercase -> lowercase 'a' (97) *)
  (* 'B' (66): uppercase -> lowercase 'b' (98) *)
  (* 'C' (67): uppercase -> lowercase 'c' (99) *)
  (* 'D' (68): uppercase -> lowercase 'd' (100) *)
  (* 'E' (69): uppercase -> lowercase 'e' (101) *)
  (* 'F' (70): uppercase -> lowercase 'f' (102) *)
  (* 'G' (71): uppercase -> lowercase 'g' (103) *)
  (* 'B' (66): uppercase -> 'b' (98) *)
  (* 'B' (66): uppercase -> 'b' (98) *)
  (* 'c' (99): lowercase -> uppercase 'C' (67) *)
  (* 'c' (99): lowercase -> 'C' (67) *)
  (* 'D' (68): uppercase -> lowercase 'd' (100) *)
  (* 'D' (68): uppercase -> lowercase 'd' (100) *)
  (* 'e' (101): lowercase -> uppercase 'E' (69) *)
  (* 'e' (101): lowercase -> uppercase 'E' (69) *)
  (* '2', '3', '4' ... remain same *)
  (* '!' ... same *)
  (* 'a' ... 'a' -> uppercase 'A' *)
  (* 'a' -> 'A' *)
  (* 'a' -> 'A' *)
  (* 'a' -> 'A' *)
  (* 'B' -> 'b' *)
  (* 'B' -> 'b' *)
  (* 'c' -> 'C' *)
  (* 'c' -> 'C' *)
  (* 'D' -> 'd' *)
  (* 'D' -> 'd' *)
  (* 'e' -> 'E' *)
  (* 'e' -> 'E' *)
  (* '2','3','4','!','!','!','1' remains same *)
  (* 'e' -> 'E' *)

  (* 最终结果为 *)
  simpl.
  reflexivity.
Qed.