(* Task
We are given two strings s and c, you have to deleted all the characters in s that are equal to any character in c
then check if the result string is palindrome.
A string is called palindrome if it reads the same backward as forward.
You should return a tuple containing the result string and True/False for the check.
Example
For s = "abcde", c = "ae", the result should be ('bcd',False)
For s = "abcdef", c = "b" the result should be ('acdef',False)
For s = "abcdedcba", c = "ab", the result should be ('cdedc',True)
*)

(* 引入所需的 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Import ListNotations.

(*
  辅助函数: list_eqb eq l1 l2
  功能: 比较两个列表 l1 和 l2 是否相等。
  它递归地检查每个元素是否相等。
*)
Fixpoint list_eqb {A : Type} (eq : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true (* 两个空列表相等 *)
  | h1 :: t1, h2 :: t2 => andb (eq h1 h2) (list_eqb eq t1 t2) (* 递归比较 *)
  | _, _ => false (* 长度不同或一个为空另一个不为空，则不相等 *)
  end.

(*
  辅助函数: my_existsb f l
  功能: 检查列表 l 中是否存在一个元素 x 使得 f x = true。
*)
Fixpoint my_existsb {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => false
  | h :: t => orb (f h) (my_existsb f t)
  end.

(*
  功能: delete_chars s c
  描述: 从列表 s 中删除所有存在于列表 c 中的字符。
  这里我们使用自定义的 my_existsb 函数。
*)
Fixpoint delete_chars (s c : list ascii) : list ascii :=
  match s with
  | [] => []
  | h :: t =>
      if my_existsb (fun x => Ascii.eqb x h) c
      then delete_chars t c
      else h :: delete_chars t c
  end.

(*
  功能: is_palindrome s
  描述: 检查列表 s 是否为回文。
  这里我们使用自定义的 list_eqb 函数。
*)
Definition is_palindrome (s : list ascii) : bool :=
  list_eqb Ascii.eqb s (rev s).

(*
  规约: program_spec s c output
  描述: 这个规约定义了程序的预期行为。
*)
Definition program_spec (s c : list ascii) (output : list ascii * bool) : Prop :=
  let (res_s, res_b) := output in
  res_s = delete_chars s c /\ res_b = is_palindrome res_s.