(* Find the shortest palindrome that begins with a supplied string.
Algorithm idea is simple:
- Find the longest postfix of supplied string that is a palindrome.
- Append to the end of the string reverse of a string prefix that comes before the palindromic suffix.
>>> make_palindrome('')
''
>>> make_palindrome('cat')
'catac'
>>> make_palindrome('cata')
'catac'
*)

(* Spec(input, output) :=

prefix(input, output) ∧
palindrome(output) ∧
∀ p, 
  (prefix(input, p) ∧ palindrome(p)) → length(output) ≤ length(p)) *)

From Coq Require Import Ascii List Arith Lia.
Import ListNotations.

(* 前缀定义：l1 是 l2 的前缀 *)
Definition prefix  (l1 l2 : list ascii) : Prop :=
  exists rest : list ascii, l2 = l1 ++ rest.

(* 回文定义：反转后等于自己 *)
Definition palindrome  (l : list ascii) : Prop :=
  l = rev l.

Definition pre  : Prop := True.

(* 规格定义：最短的回文，且以 input 为前缀 *)
Definition Spec (input output : list ascii) : Prop :=
  prefix input output /\
  palindrome output /\
  forall p : list ascii,
    prefix input p /\
    palindrome p ->
    length output <= length p.
