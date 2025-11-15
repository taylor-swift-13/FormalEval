(*def check_dict_case(dict):
"""
Given a dictionary, return True if all keys are strings in lower
case or all keys are strings in upper case, else return False.
The function should return False is the given dictionary is empty.
Examples:
check_dict_case({"a":"apple", "b":"banana"}) should return True.
check_dict_case({"a":"apple", "A":"banana", "B":"banana"}) should return False.
check_dict_case({"a":"apple", 8:"banana", "a":"apple"}) should return False.
check_dict_case({"Name":"John", "Age":"36", "City":"Houston"}) should return False.
check_dict_case({"STATE":"NC", "ZIP":"12345" }) should return True.
"""*)
Require Import Coq.Strings.String Bool.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

(* 定义字符串是否为小写的谓词 *)
Definition is_lowercase (s : string) : Prop :=
  (* Convert string to list of ascii and ensure every character is a lowercase letter *)
  let fix all_lower (l : list ascii) : Prop :=
      match l with
      | [] => True
      | c :: tl => (("a" <=? c)%char && (c <=? "z")%char = true) /\
                   all_lower tl
      end in
  all_lower (list_ascii_of_string s).

(* 定义字符串是否为大写的谓词 *)
Definition is_uppercase (s : string) : Prop :=
  (* 这里需要一个具体的实现来检查字符串中的所有字符是否都是大写字母 *)
  let fix all_upper (l : list ascii) : Prop :=
      match l with
      | [] => True
      | c :: tl => ("A" <=? c)%char && (c <=? "Z")%char = true /\
                   all_upper tl
      end in
  all_upper (list_ascii_of_string s).

(* 定义字典的类型，这里使用从字符串到字符串的关联列表 *)
Definition dictionary := list (string * string).

(* check_dict_case 函数的规约 *)
Definition check_dict_case_spec (d : dictionary) (output : bool) : Prop :=
  match d with
  | [] => output = false
  | _ =>
    ( (forall k v, In (k, v) d -> is_lowercase k) \/
      (forall k v, In (k, v) d -> is_uppercase k) )
    <-> output = true
  end.