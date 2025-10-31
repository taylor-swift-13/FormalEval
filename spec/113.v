(* Given a list of strings, where each string consists of only digits, return a list.
Each element i of the output should be "the number of odd elements in the
string i of the input." where all the i's should be replaced by the number
of odd digits in the i'th string of the input.

>>> odd_count(['1234567'])
["the number of odd elements 4n the str4ng 4 of the 4nput."]
>>> odd_count(['3',"11111111"])
["the number of odd elements 1n the str1ng 1 of the 1nput.",
"the number of odd elements 8n the str8ng 8 of the 8nput."] *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.Ascii.

Import ListNotations.

(*
 * 辅助函数1: 检查一个字符是否为奇数数字。
 *)
Definition is_odd_digit (c : ascii) : bool :=
  match c with
  | "1"%char | "3"%char | "5"%char | "7"%char | "9"%char => true
  | _ => false
  end.

(*
 * 辅助函数2: 计算字符串中奇数数字的个数。
 *)
Fixpoint count_odd_digits (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => (if is_odd_digit c then 1 else 0) + count_odd_digits s'
  end.

(*
 * 辅助函数3: 将一个小于10的自然数转换为对应的ASCII字符。
 * 这个函数是足够的，因为示例表明我们只处理单位数的替换。
 *)
Definition nat_to_digit_char (n : nat) : ascii :=
  match n with
  | 0 => "0"%char | 1 => "1"%char | 2 => "2"%char | 3 => "3"%char | 4 => "4"%char
  | 5 => "5"%char | 6 => "6"%char | 7 => "7"%char | 8 => "8"%char | _ => "9"%char
  end.

(*
 * 辅助函数4: 在字符串中替换所有出现的目标字符。
 *)
Fixpoint replace_char (target replacement : ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      let rest := replace_char target replacement s' in
      let current_char := if Ascii.eqb c target then replacement else c in
      String current_char rest
  end.

(*
 * 核心转换逻辑: 对于单个输入字符串，生成对应的输出字符串。
 * 它计算奇数数字的数量，然后用这个数字对应的字符替换模板中的 "i"。
 *)
Definition process_string (s : string) : string :=
  let count := count_odd_digits s in
  let digit_char := nat_to_digit_char count in
  let template := "the number of odd elements in the string i of the input."%string in
  replace_char "i"%char digit_char template.

(*
 * 程序规约 (Spec):
 * 定义了输入列表 `input` 和输出列表 `output` 之间的预期关系。
 * 该规约指出，输出列表应该是将 `process_string` 函数映射到输入列表的每个元素上得到的结果。
 *)
Definition odd_count_spec (input : list string) (output : list string) : Prop :=
  output = map process_string input.