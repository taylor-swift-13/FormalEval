(* Given a string s and a natural number n, you have been tasked to implement
a function that returns a list of all words from string s that contain exactly
n consonants, in order these words appear in the string s.
If the string s is empty then the function should return an empty list.
Note: you may assume the input string contains only letters and spaces.
Examples:
select_words("Mary had a little lamb", 4) ==> ["little"]
select_words("Mary had a little lamb", 3) ==> ["Mary", "lamb"]
select_words("simple white space", 2) ==> []
select_words("Hello world", 4) ==> ["world"]
select_words("Uncle sam", 3) ==> ["Uncle"] *)

(* 引入所需的标准库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* 辅助函数：判断一个 ascii 字符是否为元音 *)
Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

(* 辅助函数：计算一个单词（list ascii）中的辅音数量 *)
Fixpoint count_consonants (word : list ascii) : nat :=
  match word with
  | [] => 0
  | h :: t =>
    (if negb (is_vowel h) then 1 else 0) + count_consonants t
  end.

(* 辅助函数：将一个句子（list ascii）按空格分割成单词列表（list (list ascii)） *)
Definition split_words (s : list ascii) : list (list ascii) :=
  let space := " "%char in
  (* 使用 'let fix' 来定义一个局部的递归辅助函数 *)
  let fix aux (current_word : list ascii) (remaining_list : list ascii) : list (list ascii) :=
    match remaining_list with
    | [] =>
      (* 当列表结束时，根据 current_word 是否为空来决定最后的行为 *)
      match current_word with
      | [] => [] (* 当前单词为空，则返回空列表 *)
      | _ => [rev current_word] (* 否则返回包含当前单词的列表 *)
      end
    | h :: t =>
      if Ascii.eqb h space then
        (* 遇到空格时，根据 current_word 是否为空来决定行为 *)
        match current_word with
        | [] => aux [] t (* 当前单词为空（连续空格），则继续处理，忽略这个空格 *)
        | _ => (rev current_word) :: aux [] t (* 否则，将当前单词加入结果，并开始新单词 *)
        end
      else
        (* 非空格字符，累加到 current_word 中 *)
        aux (h :: current_word) t
    end
  (* 主函数体调用该局部辅助函数 *)
  in aux [] s.

(*
  程序规约 (Spec)
  它描述了输入 (s : list ascii) 和 (n : nat) 与输出 (res : list (list ascii)) 之间的关系。
*)
Definition select_words_spec (s : list ascii) (n : nat) (res : list (list ascii)) : Prop :=
  res = filter (fun w => Nat.eqb (count_consonants w) n) (split_words s).