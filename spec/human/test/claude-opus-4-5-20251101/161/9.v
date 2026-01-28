Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope string_scope.

(* 判断一个 ascii 字符是否为小写字母 *)
Definition is_lower_alpha (a : ascii) : bool :=
  (("a"%char <=? a)%char && (a <=? "z"%char)%char).

(* 判断一个 ascii 字符是否为大写字母 *)
Definition is_upper_alpha (a : ascii) : bool :=
  (("A"%char <=? a)%char && (a <=? "Z"%char)%char).

(* 判断一个 ascii 字符是否为字母 *)
Definition is_letter_dec (a : ascii) : bool :=
  is_lower_alpha a || is_upper_alpha a.

(* 将小写字母转为大写 *)
Definition my_uppercase (a : ascii) : ascii :=
  if is_lower_alpha a
  then ascii_of_nat (nat_of_ascii a - 32)
  else a.

(* 将大写字母转为小写 *)
Definition my_lowercase (a : ascii) : ascii :=
  if is_upper_alpha a
  then ascii_of_nat (nat_of_ascii a + 32)
  else a.

(* 转换字母的大小写 *)
Definition change_case (a : ascii) : ascii :=
  if is_lower_alpha a then
    my_uppercase a
  else if is_upper_alpha a then
    my_lowercase a
  else
    a.

(* 判断列表是否包含字母 *)
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

Definition problem_161_pre (s : string) : Prop := True.

Definition problem_161_spec (s s' : string) : Prop :=
  s' = solve_impl s.

Example test_solve_empty : solve_impl "" = ""%string.
Proof.
  unfold solve_impl.
  simpl.
  reflexivity.
Qed.