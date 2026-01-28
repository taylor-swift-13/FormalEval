Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

(* 辅助函数：检查一个字符是否是元音 *)
Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

(* 辅助函数：转换字母的大小写 *)
Definition swap_case (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if andb (leb 65 n) (leb n 90) (* 是大写字母吗？ *)
  then ascii_of_nat (n + 32) (* 转换为小写 *)
  else if andb (leb 97 n) (leb n 122) (* 是小写字母吗？ *)
  then ascii_of_nat (n - 32) (* 转换为大写 *)
  else c. (* 不是字母，保持原样 *)

(* 辅助函数：将元音替换为两个位置之后的字母 *)
Definition replace_vowel (c : ascii) : ascii :=
  match c with
  | "a"%char => "c"%char | "e"%char => "g"%char | "i"%char => "k"%char | "o"%char => "q"%char | "u"%char => "w"%char
  | "A"%char => "C"%char | "E"%char => "G"%char | "I"%char => "K"%char | "O"%char => "Q"%char | "U"%char => "W"%char
  | _ => c
  end.

Definition encode_char_spec (c_in c_out : ascii) : Prop :=
  let c_swapped := swap_case c_in in
  if is_vowel c_in
  then c_out = replace_vowel c_swapped
  else c_out = c_swapped.

(* 预条件：消息只包含英文字母大小写或空格 *)
Definition problem_93_pre (s_in : string) : Prop :=
  let l_in := list_ascii_of_string s_in in
  Forall (fun c => let n := nat_of_ascii c in (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122) \/ n = 32) l_in.

(* 完整 encode 函数的规约 *)
Definition problem_93_spec (s_in s_out : string) : Prop :=
  let l_in := list_ascii_of_string s_in in
  let l_out := list_ascii_of_string s_out in
  Forall2 encode_char_spec l_in l_out.

(* Test case verification *)
Example test_problem_93 : problem_93_spec "The quick brown fox jumps over lazythe lazy dog" "tHG QWKCK BRQWN FQX JWMPS QVGR LCZYTHG LCZY DQG".
Proof.
  (* Unfold the main specification *)
  unfold problem_93_spec.
  
  (* Simplify the string to list conversion for concrete strings *)
  simpl.
  
  (* Apply constructors for Forall2 repeatedly to break down the list *)
  repeat constructor.
  
  (* Now we have subgoals for each character pair. 
     We can solve them all by unfolding the character spec, 
     simplifying the computation, and checking equality. *)
  all: unfold encode_char_spec.
  all: simpl.
  all: reflexivity.
Qed.