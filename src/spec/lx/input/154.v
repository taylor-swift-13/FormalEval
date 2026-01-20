(* def cycpattern_check(a , b):
"""You are given 2 words. You need to return True if the second word or any of its rotations is a substring in the first word
cycpattern_check("abcd","abd") => False
cycpattern_check("hello","ell") => True
cycpattern_check("whassup","psus") => False
cycpattern_check("abab","baa") => True
cycpattern_check("efef","eeff") => False
cycpattern_check("himenss","simen") => True

""" *)
(* 引入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Import ListNotations.

(* 定义：sub 是 main 的子串 *)
Definition is_substring (sub main : list ascii) : Prop :=
  exists prefix suffix, main = prefix ++ sub ++ suffix.

(* 定义：r 是 b 的一个循环旋转 *)
Definition is_rotation_of (r b : list ascii) : Prop :=
  exists p1 p2, b = p1 ++ p2 /\ r = p2 ++ p1.

(* cycpattern_check 函数的程序规约 *)
Definition cycpattern_check_spec (a b : list ascii) (res : bool) : Prop :=
  res = true <-> (exists b', is_rotation_of b' b /\ is_substring b' a).