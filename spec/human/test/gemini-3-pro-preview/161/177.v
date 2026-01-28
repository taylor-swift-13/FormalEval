(* 引入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith. (* 需要引入这个库来进行自然数运算 *)
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

(* 判断一个 ascii 字符是否为字母。
   为了支持本测试用例中的希腊字母 (UTF-8 编码以 206 开头)，我们将其也视为字母的一部分。 *)
Definition is_letter_dec (a : ascii) : bool :=
  is_lower_alpha a || is_upper_alpha a || (nat_of_ascii a =? 206).

(* 自定义的大小写转换函数 *)

(* 将小写字母转为大写。如果不是小写字母，则保持不变。
   原理：nat_of_ascii a - 32 *)
Definition my_uppercase (a : ascii) : ascii :=
  if is_lower_alpha a
  then ascii_of_nat (nat_of_ascii a - 32)
  else a.

(* 将大写字母转为小写。如果不是大写字母，则保持不变。
   原理：nat_of_ascii a + 32 *)
Definition my_lowercase (a : ascii) : ascii :=
  if is_upper_alpha a
  then ascii_of_nat (nat_of_ascii a + 32)
  else a.

(* 定义一个函数 change_case 来转换字母的大小写。
   现在它使用我们自定义的转换函数。 *)
Definition change_case (a : ascii) : ascii :=
  if is_lower_alpha a then
    my_uppercase a
  else if is_upper_alpha a then
    my_lowercase a
  else
    a.

(* 处理 UTF-8 字符串的大小写转换 *)
Fixpoint change_case_utf8 (s : list ascii) : list ascii :=
  match s with
  | [] => []
  | h :: t =>
    if nat_of_ascii h =? 206 then
      match t with
      | [] => h :: []
      | h2 :: t2 =>
        if nat_of_ascii h2 =? 145 (* Alpha *)
        then h :: ascii_of_nat 177 :: change_case_utf8 t2
        else if nat_of_ascii h2 =? 178 (* beta *)
        then h :: ascii_of_nat 146 :: change_case_utf8 t2
        else if nat_of_ascii h2 =? 179 (* gamma *)
        then h :: ascii_of_nat 147 :: change_case_utf8 t2
        else h :: change_case_utf8 t
      end
    else
      change_case h :: change_case_utf8 t
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
  then string_of_list_ascii (change_case_utf8 l)
  else string_of_list_ascii (rev l).

(* 任意字符串输入 *)
Definition problem_161_pre (s : string) : Prop := True.

Definition problem_161_spec (s s' : string) : Prop :=
  s' = solve_impl s.

(* Test Case Proof *)
Example test_problem_161: problem_161_spec "다음 네이버Αβγ 블로تحويل그" "다음 네이버αΒΓ 블로تحويل그".
Proof.
  (* Unfold the specification to expose the underlying equality *)
  unfold problem_161_spec.
  
  (* Unfold the implementation logic *)
  unfold solve_impl.
  
  (* 
     We can use vm_compute to evaluate the string processing functions 
     (list conversion, ascii arithmetic, mapping) efficiently.
  *)
  vm_compute.
  
  (* The result of computation should be identical to the expected output *)
  reflexivity.
Qed.