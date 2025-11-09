Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope char_scope.
(*
  char_relation 定义了单个输入字符 c_in 和输出字符 c_out 之间的关系。
  这遵循字母表向下移动 4 (2*2) 位的规则。
*)
Definition char_relation (c_in c_out : ascii) : Prop :=
  match c_in with
  | "a" => c_out = "e" | "b" => c_out = "f" | "c" => c_out = "g" | "d" => c_out = "h"
  | "e" => c_out = "i" | "f" => c_out = "j" | "g" => c_out = "k" | "h" => c_out = "l"
  | "i" => c_out = "m" | "j" => c_out = "n" | "k" => c_out = "o" | "l" => c_out = "p"
  | "m" => c_out = "q" | "n" => c_out = "r" | "o" => c_out = "s" | "p" => c_out = "t"
  | "q" => c_out = "u" | "r" => c_out = "v" | "s" => c_out = "w" | "t" => c_out = "x"
  | "u" => c_out = "y" | "v" => c_out = "z" | "w" => c_out = "a" | "x" => c_out = "b"
  | "y" => c_out = "c" | "z" => c_out = "d"
  (* 对于非小写字母的任何其他字符，它保持不变 *)
  | _ => c_out = c_in
  end.

(*
  encrypt_spec (程序规约)
  它规定：
  1. 输入列表 s 和输出列表 output 的长度必须相等。
  2. 对于两个列表中每个位置上对应的字符 (c_in, c_out)，
     它们必须满足 char_relation 定义的关系。
  Coq 中的 Forall2 谓词简洁地表达了这两个条件。
*)
Definition encrypt_spec (s : list ascii) (output : list ascii) : Prop :=
  Forall2 char_relation s output.