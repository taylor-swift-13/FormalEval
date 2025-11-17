(* def find_max(words):
"""Write a function that accepts a list of strings.
The list contains different words. Return the word with maximum number
of unique characters. If multiple strings have maximum number of unique
characters, return the one which comes first in lexicographical order.

find_max(["name", "of", "string"]) == "string"
find_max(["name", "enam", "game"]) == "enam"
find_max(["aaaaaaa", "bb" ,"cc"]) == ""aaaaaaa"
 *)
(* 导入必要的 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Local Open Scope string_scope.

(* 输入单词列表需非空 *)
Definition Pre (words : list string) : Prop := words <> [].

(*
  辅助定义 1：检查一个元素是否在一个列表中（使用布尔相等性测试）。
  这是 `remove_duplicates` 函数需要用到的辅助函数。
*)
Fixpoint is_in (eqb : ascii -> ascii -> bool) (x : ascii) (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' => if eqb x c then true else is_in eqb x s'
  end.

(*
  辅助定义 2：移除列表中的重复元素（替代 `nub` 函数）。
  这个函数从左到右遍历列表，如果一个元素在结果中还不存在，就将它加入。
*)
Fixpoint remove_duplicates (eqb : ascii -> ascii -> bool) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
    let rest := remove_duplicates eqb s' in
    if is_in eqb c rest
    then rest
    else String c rest
  end.

(*
  辅助定义 3：计算一个 `list ascii` 中唯一字符的数量。
  这里我们使用自己定义的 `remove_duplicates` 函数。
*)
(* 将 string 转换为 list ascii 的辅助函数 *)
Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

(* 计算字符串中唯一字符的数量 *)
Definition count_unique_chars (s : string) : nat :=
  length (remove_duplicates Ascii.eqb s).

(*
  辅助定义 4：关于 `list ascii` 的字典序小于等于关系的命题。
*)
Fixpoint lexico_le (s1 s2 : list ascii) : Prop :=
  match s1, s2 with
  | [], _ => True
  | _::_, [] => False
  | c1::s1_tail, c2::s2_tail =>
      (nat_of_ascii c1 < nat_of_ascii c2) \/ (c1 = c2 /\ lexico_le s1_tail s2_tail)
  end.

(* 字符串的字典序比较（基于其 ascii 列表表示） *)
Definition lexico_le_string (a b : string) : Prop :=
  lexico_le (string_to_list a) (string_to_list b).

(*
  find_max 函数的程序规约 (Spec)。
  这个规约描述了输入 `words` 和输出 `result` 之间必须满足的关系。
*)
Definition find_max_spec (words : list string) (result : string) : Prop :=
  (*
    条件 1:
    输出的 `result` 必须是输入 `words` 列表中的一个元素。
   *)
  In result words /\
  (*
    条件 2:
    对于 `words` 列表中的任何一个单词 `w`，必须满足以下两个子条件之一：
   *)
  forall (w : string), In w words ->
    (* a) `result` 的唯一字符数严格大于 `w` 的唯一字符数。*)
    (count_unique_chars result > count_unique_chars w) \/
    (*
       b) `result` 和 `w` 的唯一字符数相等，并且 `result` 在字典序上
          小于或等于 `w`。
     *)
    ((count_unique_chars result = count_unique_chars w) /\ lexico_le_string result w).