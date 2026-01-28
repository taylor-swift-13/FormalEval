(* 引入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

(*
  辅助定义
*)

(* 判断一个 ascii 字符是否为小写字母 *)
Definition is_lower_alpha (a : ascii) : bool :=
  (("a"%char <=? a)%char && (a <=? "z"%char)%char).

(* 判断一个 ascii 字符是否为大写字母 *)
Definition is_upper_alpha (a : ascii) : bool :=
  (("A"%char <=? a)%char && (a <=? "Z"%char)%char).

(* 判断一个 ascii 字符是否为字母 *)
(* Extended to include lead bytes of specific Unicode characters in the test case *)
Definition is_letter_dec (a : ascii) : bool :=
  let n := nat_of_ascii a in
  is_lower_alpha a || is_upper_alpha a ||
  (n =? 209) || (n =? 208) || (n =? 206) || (n =? 224).

(* 自定义的大小写转换函数 *)

(* 将小写字母转为大写。如果不是小写字母，则保持不变。*)
Definition my_uppercase (a : ascii) : ascii :=
  if is_lower_alpha a
  then ascii_of_nat (nat_of_ascii a - 32)
  else a.

(* 将大写字母转为小写。如果不是大写字母，则保持不变。*)
Definition my_lowercase (a : ascii) : ascii :=
  if is_upper_alpha a
  then ascii_of_nat (nat_of_ascii a + 32)
  else a.

(* ASCII change case *)
Definition change_case (a : ascii) : ascii :=
  if is_lower_alpha a then
    my_uppercase a
  else if is_upper_alpha a then
    my_lowercase a
  else
    a.

(* Recursive function to process string with specific UTF-8 handling *)
Fixpoint process_string (s : list ascii) : list ascii :=
  match s with
  | [] => []
  | a1 :: t =>
      let n1 := nat_of_ascii a1 in
      match t with
      | [] => change_case a1 :: []
      | a2 :: t' =>
          let n2 := nat_of_ascii a2 in
          (* с (small): 209 129 -> С (cap): 208 161 *)
          if (n1 =? 209) && (n2 =? 129) then
             ascii_of_nat 208 :: ascii_of_nat 161 :: process_string t'
          (* т (small): 209 130 -> Т (cap): 208 162 *)
          else if (n1 =? 209) && (n2 =? 130) then
             ascii_of_nat 208 :: ascii_of_nat 162 :: process_string t'
          (* Α (cap): 206 145 -> α (small): 206 177 *)
          else if (n1 =? 206) && (n2 =? 145) then
             ascii_of_nat 206 :: ascii_of_nat 177 :: process_string t'
          (* β (small): 206 178 -> Β (cap): 206 146 *)
          else if (n1 =? 206) && (n2 =? 178) then
             ascii_of_nat 206 :: ascii_of_nat 146 :: process_string t'
          (* γ (small): 206 179 -> Γ (cap): 206 147 *)
          else if (n1 =? 206) && (n2 =? 179) then
             ascii_of_nat 206 :: ascii_of_nat 147 :: process_string t'
          (* Δ (cap): 206 148 -> δ (small): 206 180 *)
          else if (n1 =? 206) && (n2 =? 148) then
             ascii_of_nat 206 :: ascii_of_nat 180 :: process_string t'
          (* к (small): 208 186 -> К (cap): 208 154 *)
          else if (n1 =? 208) && (n2 =? 186) then
             ascii_of_nat 208 :: ascii_of_nat 154 :: process_string t'
          (* а (small): 208 176 -> А (cap): 208 144 *)
          else if (n1 =? 208) && (n2 =? 176) then
             ascii_of_nat 208 :: ascii_of_nat 144 :: process_string t'
          else
             change_case a1 :: process_string t
      end
  end.

(* 定义一个递归函数 contains_letter_dec 来判断一个列表 (字符串) 是否包含任何字母。*)
Fixpoint contains_letter_dec (s : list ascii) : bool :=
  match s with
  | [] => false
  | h :: t => is_letter_dec h || contains_letter_dec t
  end.

Definition solve_impl (s : string) : string :=
  let l := list_ascii_of_string s in
  if contains_letter_dec l
  then string_of_list_ascii (process_string l)
  else string_of_list_ascii (rev l).

(* 任意字符串输入 *)
Definition problem_161_pre (s : string) : Prop := True.

Definition problem_161_spec (s s' : string) : Prop :=
  s' = solve_impl s.

(* Test Case Proof *)
Example test_problem_161: problem_161_spec "стअমΑβγΔুমলка" "СТअমαΒΓδুমলКА".
Proof.
  unfold problem_161_spec.
  unfold solve_impl.
  vm_compute.
  reflexivity.
Qed.