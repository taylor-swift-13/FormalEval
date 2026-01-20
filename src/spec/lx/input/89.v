Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Import ListNotations.

(*
  char_relation 定义了单个输入字符 c_in 和输出字符 c_out 之间的关系。
  这遵循字母表向下移动 4 (2*2) 位的规则。
*)
Definition char_relation (c_in c_out : ascii) : Prop :=
  match c_in with
  | "a"%char => c_out = "e"%char | "b"%char => c_out = "f"%char | "c"%char => c_out = "g"%char | "d"%char => c_out = "h"%char
  | "e"%char => c_out = "i"%char | "f"%char => c_out = "j"%char | "g"%char => c_out = "k"%char | "h"%char => c_out = "l"%char
  | "i"%char => c_out = "m"%char | "j"%char => c_out = "n"%char | "k"%char => c_out = "o"%char | "l"%char => c_out = "p"%char
  | "m"%char => c_out = "q"%char | "n"%char => c_out = "r"%char | "o"%char => c_out = "s"%char | "p"%char => c_out = "t"%char
  | "q"%char => c_out = "u"%char | "r"%char => c_out = "v"%char | "s"%char => c_out = "w"%char | "t"%char => c_out = "x"%char
  | "u"%char => c_out = "y"%char | "v"%char => c_out = "z"%char | "w"%char => c_out = "a"%char | "x"%char => c_out = "b"%char
  | "y"%char => c_out = "c"%char | "z"%char => c_out = "d"%char
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