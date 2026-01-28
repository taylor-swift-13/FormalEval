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

(* 判断一个 ascii 字符是否为字母 *)
Definition is_letter_dec (a : ascii) : bool :=
  is_lower_alpha a || is_upper_alpha a.

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

(* 定义一个递归函数 contains_letter_dec 来判断一个列表 (字符串) 是否包含任何字母。*)
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

(* 任意字符串输入 *)
Definition problem_161_pre (s : string) : Prop := True.

Definition problem_161_spec (s s' : string) : Prop :=
  s' = solve_impl s.

(* Helper to construct string from list of nats (representing bytes) *)
Definition s_from_nats (l : list nat) : string :=
  string_of_list_ascii (map ascii_of_nat l).

(* 
   Test Case: input = ["😂😎😎😀😂😎"], output = "😎😂😀😎😎😂"
   
   Since Coq's standard string literal syntax does not support multi-byte characters 
   (emojis) directly, and the algorithm treats non-letter characters uniformly, 
   we represent the emojis as distinct ASCII codes that are not letters.
   
   Mapping:
   😂 (Emoji 1) -> ASCII 1
   😎 (Emoji 2) -> ASCII 2
   😀 (Emoji 3) -> ASCII 3
   
   Input sequence:  Emoji 1, Emoji 2, Emoji 2, Emoji 3, Emoji 1, Emoji 2
   Encoded input:   [1; 2; 2; 3; 1; 2]
   
   Expected output: Emoji 2, Emoji 1, Emoji 3, Emoji 2, Emoji 2, Emoji 1
   Encoded output:  [2; 1; 3; 2; 2; 1]
*)

Definition test_input : string := s_from_nats [1; 2; 2; 3; 1; 2].
Definition test_output : string := s_from_nats [2; 1; 3; 2; 2; 1].

(* Test Case Proof *)
Example test_problem_161: problem_161_spec test_input test_output.
Proof.
  (* Unfold the specification to expose the underlying equality *)
  unfold problem_161_spec.
  
  (* Unfold the implementation logic *)
  unfold solve_impl.
  
  (* Unfold helper definitions *)
  unfold test_input, test_output, s_from_nats.
  
  (* 
     We can use vm_compute to evaluate the string processing functions.
     The input string contains no letters (ASCII 1, 2, 3), so `contains_letter_dec` 
     returns false, and the `else` branch (reverse) is taken.
  *)
  vm_compute.
  
  (* The result of computation should be identical to the expected output *)
  reflexivity.
Qed.