(* def is_bored(S):
"""
You'll be given a string of words, and your task is to count the number
of boredoms. A boredom is a sentence that starts with the word "I".
Sentences are delimited by '.', '?' or '!'.

For example:
>>> is_bored("Hello world")
0
>>> is_bored("The sky is blue. The sun is shining. I love this weather")
1
""" *)
(* 引入 Coq 的标准库，用于字符串、字符、列表和自然数算术 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* 打开字符串作用域以便使用 "s" 这样的字符串字面量 *)
Open Scope string_scope.

(*
  辅助定义 1: is_sentence_delimiter
  一个判定谓词，用于检查一个字符是否为句子分隔符。
*)
Definition is_sentence_delimiter (c : ascii) : bool :=
  match c with
  | "."%char | "?"%char | "!"%char => true
  | _ => false
  end.

(*
  辅助定义 2: split
  一个函数，它根据给定的谓词 p 将字符串分割成字符串列表。
*)
Fixpoint split_aux (p : ascii -> bool) (s : string) (current : string) : list string :=
  match s with
  | "" => [current]
  | String c rest =>
      if p c then
        current :: split_aux p rest ""
      else
        split_aux p rest (current ++ String c "")
  end.

Definition split (p : ascii -> bool) (s : string) : list string :=
  split_aux p s "".

(*
  辅助定义 3: is_whitespace
  一个判定谓词，用于检查一个字符是否为空白字符。
*)
Definition is_whitespace (c : ascii) : bool :=
  match c with
  | " "%char => true
  | _ => false
  end.

(*
  辅助定义 4: trim_leading_whitespace
  一个函数，用于移除字符串头部的所有空白字符。
  这用于模拟 re.split(r'[.?!]\s*') 的行为，即消耗分隔符后的空格。
*)
Fixpoint trim_leading_whitespace (s : string) : string :=
  match s with
  | String c rest => if is_whitespace c then trim_leading_whitespace rest else s
  | "" => ""
  end.

(*
  辅助定义 5: is_boredom_sentence_new
  一个判定谓词，根据新的 Python 实现来检查一个句子是否为“boredom”。
  它直接检查字符串是否以 "I " 开头。
*)
Definition is_boredom_sentence_new (s : string) : bool :=
  prefix "I " s.

(*
  程序规约 (Program Specification): is_bored_spec_new
  这个规约描述了输入字符串 S 和期望输出 output 之间的关系。
  它声明：输出值 output 必须等于通过以下方式计算出的“boredom”句子的数量：
  1. 将输入字符串 S 按句子分隔符分割成一个初步的句子列表。
  2. 对列表中的每个字符串进行清理，移除其前导空格，以模拟 Python 中 re.split 的行为。
  3. 过滤出列表中所有满足 is_boredom_sentence_new 谓词的句子。
  4. 计算过滤后列表的长度。
*)
Definition is_bored_spec_new (S : string) (output : nat) : Prop :=
  let initial_sentences := split is_sentence_delimiter S in
  let cleaned_sentences := map trim_leading_whitespace initial_sentences in
  let boredoms := filter is_boredom_sentence_new cleaned_sentences in
  output = length boredoms.