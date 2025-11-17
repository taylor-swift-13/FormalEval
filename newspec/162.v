(* def string_to_md5(text):
"""
Given a string 'text', return its md5 hash equivalent string.
If 'text' is an empty string, return None.

>>> string_to_md5('Hello world') == '3e25960a79dbc69b674cd4ec67a72c62'
""" *)
(* 导入所需的基础库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

(* 任意字符串输入 *)
Definition Pre (text : list ascii) : Prop := True.

(*
  我们无法在 Coq 的规约中直接计算 MD5。
  因此，我们声明一个“参数”（Parameter），把它当作一个已知的、理想的 MD5 函数。
  这个函数接受一个 `list ascii`（字符串）并返回其 MD5 哈希值的 `list ascii` 形式。
*)
Parameter md5_hash : list ascii -> list ascii.

(*
  程序 string_to_md5 的规约（Specification）。
  它定义了输入 `text` (一个 list ascii) 和输出 `output` (一个 option (list ascii)) 之间的关系。
  这个关系是一个命题（Prop）。
*)
Definition string_to_md5_spec (text : list ascii) (output : option (list ascii)) : Prop :=
  match text with
  | [] => (* 情况1: 如果输入 'text' 是一个空列表 *)
      output = None (* 那么输出必须是 None *)
  | _ :: _ => (* 情况2: 如果输入 'text' 是一个非空列表 *)
      output = Some (md5_hash text) (* 那么输出必须是 Some (md5_hash text) *)
  end.