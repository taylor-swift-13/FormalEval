(* You will be given a string of words separated by commas or spaces. Your task is
to split the string into words and return an array of the words.

For example:
words_string("Hi, my name is John") == ["Hi", "my", "name", "is", "John"]
words_string("One, two, three, four, five, six") == ["One", "two", "three", "four", "five", "six"] *)

(* 导入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

(* 1. 定义分隔符 (无变化) *)
Definition is_delimiter (c : ascii) : bool :=
  match c with
  | ","%char | " "%char => true
  | _ => false
  end.

(* 2. 实现字符串拆分函数 (最终结构) *)

(* 步骤1: 定义一个辅助函数 *)
Fixpoint words_string_aux (current_word : list ascii) (input : list ascii) : list (list ascii) :=
  match input with
  | [] =>
    (* 输入列表结束，返回最后一个单词（如果存在） *)
    match current_word with
    | [] => []
    | _ => [current_word]
    end
  | c :: cs =>
    if is_delimiter c then
      (* 遇到分隔符，完成当前单词 *)
      match current_word with
      | [] => words_string_aux [] cs (* 忽略连续的分隔符 *)
      | _ => current_word :: words_string_aux [] cs (* 完成单词并开始新的 *)
      end
    else
      (* 非分隔符，追加到当前单词 *)
      words_string_aux (current_word ++ [c]) cs
  end.

(* 步骤2: 定义主函数作为一个简单的、非递归的包装器 *)
Definition words_string_list (s : list ascii) : list (list ascii) :=
  (* 调用辅助函数并传入初始状态：当前单词为空列表，输入为整个字符串 *)
  words_string_aux [] s.

(* 3. 程序规约 (Spec)  *)
Definition non_delimiter_char (c : ascii) : Prop :=
  is_delimiter c = false.

Definition words_string_list_spec (s : list ascii) (result : list (list ascii)) : Prop :=
  result = words_string_list s /\
  Forall (fun word => Forall non_delimiter_char word) result.




