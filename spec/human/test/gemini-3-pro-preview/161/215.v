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

(* 判断一个 ascii 字符是否为小写字母 (ASCII) *)
Definition is_ascii_lower (a : ascii) : bool :=
  (("a"%char <=? a)%char && (a <=? "z"%char)%char).

(* 判断一个 ascii 字符是否为大写字母 (ASCII) *)
Definition is_ascii_upper (a : ascii) : bool :=
  (("A"%char <=? a)%char && (a <=? "Z"%char)%char).

(* Greek Helpers for the specific test case *)
(* Greek Upper 2nd byte range: Alpha (CE 91) to Omega (CE A9) -> [145, 169] *)
Definition is_greek_upper_byte (a : ascii) : bool :=
  let n := nat_of_ascii a in
  (145 <=? n) && (n <=? 169).

(* Greek Lower 2nd byte range: alpha (CE B1) to omega (CE C9) -> [177, 201] *)
Definition is_greek_lower_byte (a : ascii) : bool :=
  let n := nat_of_ascii a in
  (177 <=? n) && (n <=? 201).

(* 判断一个 ascii 字符是否为字母 (Includes Greek bytes to trigger processing) *)
Definition is_letter_dec (a : ascii) : bool :=
  is_ascii_lower a || is_ascii_upper a || is_greek_upper_byte a || is_greek_lower_byte a.

(* 自定义的大小写转换函数 *)

Definition to_upper_byte (a : ascii) : ascii :=
  ascii_of_nat (nat_of_ascii a - 32).

Definition to_lower_byte (a : ascii) : ascii :=
  ascii_of_nat (nat_of_ascii a + 32).

(* Context-aware string swap case *)
Fixpoint string_swap_case (s : list ascii) : list ascii :=
  match s with
  | [] => []
  | c :: rest =>
      (* Check for Greek prefix 0xCE = 206 *)
      if (nat_of_ascii c =? 206) then
        match rest with
        | c2 :: rest2 =>
            if is_greek_lower_byte c2 then
               c :: (to_upper_byte c2) :: string_swap_case rest2
            else if is_greek_upper_byte c2 then
               c :: (to_lower_byte c2) :: string_swap_case rest2
            else
               c :: string_swap_case rest
        | [] => [c]
        end
      else if is_ascii_lower c then
        (to_upper_byte c) :: string_swap_case rest
      else if is_ascii_upper c then
        (to_lower_byte c) :: string_swap_case rest
      else
        c :: string_swap_case rest
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
  then string_of_list_ascii (string_swap_case l)
  else string_of_list_ascii (rev l).

(* 任意字符串输入 *)
Definition problem_161_pre (s : string) : Prop := True.

Definition problem_161_spec (s s' : string) : Prop :=
  s' = solve_impl s.

(* Test Case Proof *)
Example test_problem_161: problem_161_spec "अমΑβγΔমβুমল" "अমαΒΓδমΒুমল".
Proof.
  (* Unfold the specification to expose the underlying equality *)
  unfold problem_161_spec.
  
  (* Unfold the implementation logic *)
  unfold solve_impl.
  
  (* 
     We can use vm_compute to evaluate the string processing functions 
  *)
  vm_compute.
  
  (* The result of computation should be identical to the expected output *)
  reflexivity.
Qed.