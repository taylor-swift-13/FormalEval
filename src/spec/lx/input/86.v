(* def anti_shuffle(s):
"""
Write a function that takes a string and returns an ordered version of it.
Ordered version of string, is a string where all words (separated by space)
are replaced by a new word where all the characters arranged in
ascending order based on ascii value.
Note: You should keep the order of words and blank spaces in the sentence.

For example:
anti_shuffle('Hi') returns 'Hi'
anti_shuffle('hello') returns 'ehllo'
anti_shuffle('Hello World!!!') returns 'Hello !!!Wdlor'
""" *)
(* 引入 Coq 标准库中关于字符串、列表、算术和置换的理论 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.

Import ListNotations.

(*
 * 辅助定义 1：is_space
 * 一个断言，当且仅当字符 c 是空格时为真。
 *)
Definition is_space (c : ascii) : Prop := c = " "%char.

(*
 * 辅助定义 2：is_sorted
 * 一个断言，当且仅当一个字符列表中的所有字符都根据其 ASCII 值按升序排列时为真。
 *)
Fixpoint is_sorted (s : list ascii) : Prop :=
  match s with
  | [] => True
  | c1 :: tl =>
      match tl with
      | [] => True
      | c2 :: _ => (nat_of_ascii c1 <= nat_of_ascii c2) /\ is_sorted tl
      end
  end.

(*
 * 程序规约：anti_shuffle_spec
 *
 * 这个规约定义了输入列表 's' 和输出列表 's_out' 必须满足的关系。
 * 它由三个核心属性构成。
 *)
Definition anti_shuffle_spec (s s_out : list ascii) : Prop :=
  (* 属性 1: 输出列表的长度必须与输入列表的长度完全相等。 *)
  length s = length s_out /\

  (* 属性 2: 空格和非空格字符的位置必须保持不变。
     也就是说，在任意一个位置 i，如果输入字符是空格，那么输出字符也必须是空格，反之亦然。 *)
  (forall i, i < length s ->
    (is_space (nth i s " "%char) <-> is_space (nth i s_out " "%char))) /\

  (* 属性 3: 对于输入列表 's' 中的任何一个“单词”（即由非空格字符组成的最大连续片段），
     输出列表 's_out' 在相同位置的对应片段，必须是原片段的一个已排序的置换。 *)
  (forall start end_,
    (* 以下逻辑用于精确地定义一个从 'start' 到 'end_' 的最大连续单词片段。 *)
    (
      (* (a) 该片段必须在列表的有效范围内。 *)
      start <= end_ /\ end_ < length s /\

      (* (b) 该片段中的所有字符都不能是空格。 *)
      (forall i, start <= i <= end_ -> ~is_space (nth i s " "%char)) /\

      (* (c) 该片段是“最大”的：它的前面要么是列表的开头，要么是一个空格。 *)
      (start = 0 \/ (start > 0 /\ is_space (nth (start - 1) s " "%char))) /\

      (* (d) 它的后面要么是列表的结尾，要么是一个空格。 *)
      (end_ + 1 = length s \/ (end_ + 1 < length s /\ is_space (nth (end_ + 1) s " "%char)))
    )
    ->
    (* 如果以上条件成立，从而确定了一个单词片段，则必须满足以下属性： *)
    (
      (* 修正：使用 firstn 和 skipn 组合来实现 sublist 的功能。 *)
      let len := end_ - start + 1 in
      let word_in  := firstn len (skipn start s) in
      let word_out := firstn len (skipn start s_out) in
      
      (* 输出片段必须是输入片段的置换（即拥有完全相同的字符和数量）。 *)
      Permutation.Permutation word_in word_out /\
      
      (* 并且输出片段必须是排序好的。 *)
      is_sorted word_out
    )
  ).