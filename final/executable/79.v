(* def decimal_to_binary(decimal):
"""You will be given a number in decimal form and your task is to convert it to
binary format. The function should return a string, with each character representing a binary
number. Each character in the string will be '0' or '1'.

There will be an extra couple of characters 'db' at the beginning and at the end of the string.
The extra characters are there to help with the format.

Examples:
decimal_to_binary(15) # returns "db1111db"
decimal_to_binary(32) # returns "db100000db"
""" *)
(* 导入Coq中处理字符串和列表所需的基础库 *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* 开启 String 作用域，以便Coq能正确解析字符串字面量 *)
Open Scope string_scope.

(*
 brief IsBinaryRepr n l 定了自然数 n 与其二进制表示（布尔列表 l）之间的关系。
 * true 代表 '1', false 代表 '0'。
 * 这是一个大端（big-endian）表示。
 *
 * 例如：IsBinaryRepr 15 [true; true; true; true]
 *       IsBinaryRepr 32 [true; false; false; false; false; false]
 *)
Inductive IsBinaryRepr : nat -> list bool -> Prop :=
  | BZ: IsBinaryRepr 0 [false]
  | B1: IsBinaryRepr 1 [true]
  | BEven (n : nat) (l : list bool) :
      n > 0 -> IsBinaryRepr n l -> IsBinaryRepr (2 * n) (l ++ [false])
  | BOdd (n : nat) (l : list bool) :
      n > 0 -> IsBinaryRepr n l -> IsBinaryRepr (2 * n + 1) (l ++ [true]).

(*
 * @brief 将布尔值列表转换为由 '0' 和 '1' 组成的字符串。
 *
 * 例如: binary_list_to_string [true; true; false; true] 会返回 "1101"
 *)
Fixpoint binary_list_to_string (l : list bool) : string :=
  match l with
  | [] => ""
  | b :: tl => (if b then "1" else "0") ++ binary_list_to_string tl
  end.

Fixpoint nat_to_binary_list_aux (n fuel : nat) : list bool :=
  match fuel with
  | O => []
  | S fuel' =>
      match n with
      | O => [false]
      | 1 => [true]
      | _ =>
          if Nat.even n then
            nat_to_binary_list_aux (n / 2) fuel' ++ [false]
          else
            nat_to_binary_list_aux ((n - 1) / 2) fuel' ++ [true]
      end
  end.

Definition nat_to_binary_list (n : nat) : list bool :=
  match n with
  | O => [false]
  | _ => nat_to_binary_list_aux n n
  end.

Definition decimal_to_binary_impl (decimal : nat) : string :=
  let bl := nat_to_binary_list decimal in
  "db" ++ binary_list_to_string bl ++ "db".

Definition decimal_to_binary_spec (decimal : nat) (output : string) : Prop :=
  output = decimal_to_binary_impl decimal.