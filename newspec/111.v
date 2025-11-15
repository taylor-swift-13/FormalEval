(* Given a string representing a space separated lowercase letters, return a dictionary
of the letter with the most repetition and containing the corresponding count.
If several letters have the same occurrence, return all of them.

Example:
histogram('a b c') == {'a': 1, 'b': 1, 'c': 1}
histogram('a b b a') == {'a': 2, 'b': 2}
histogram('a b c a b') == {'a': 2, 'b': 2}
histogram('b b b b a') == {'b': 4}
histogram('') == {}
*)

Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Import ListNotations.

(*
  程序规约 Spec
  输入：letters : list ascii (一个由字符组成的列表)
  输出：res : list (ascii * nat) (一个由 (字符, 计数值) 对组成的列表)
*)
Definition histogram_spec (letters : list ascii) (res : list (ascii * nat)) : Prop :=
  (* 找出所有唯一的字符 *)
  let unique_letters := nodup ascii_dec letters in
  match unique_letters with
  | [] => res = [] (* 如果输入列表为空，则输出也为空 *)
  | _ :: _ => (* 如果列表不为空 *)
    (* 定义一个计算单个字符在原列表中出现次数的局部函数 *)
    let count_char (c : ascii) := count_occ ascii_dec letters c in
    (* 计算所有唯一字符的出现次数 *)
    let counts := map count_char unique_letters in
    (* 找出最大的计数值 *)
    let max_count := fold_right max 0 counts in

    (*
      规约的核心：输出 res 必须精确地包含所有出现次数最多的字符及其计数值。
      这可以用两个方向的蕴含来表达。
    *)
    (* 1. "Soundness": 输出 res 中的每一个元素都必须是正确的。 *)
    (forall (p : ascii * nat), In p res ->
      let (c, n) := p in
      n = max_count /\ count_char c = max_count) /\

    (* 2. "Completeness": 每一个符合条件的字符都必须出现在输出 res 中。 *)
    (forall c, In c unique_letters ->
      count_char c = max_count ->
      In (c, max_count) res)
  end.