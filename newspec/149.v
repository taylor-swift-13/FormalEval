(* def sorted_list_sum(lst):
"""Write a function that accepts a list of strings as a parameter,
deletes the strings that have odd lengths from it,
and returns the resulted list with a sorted order,
The list is always a list of strings and never an array of numbers,
and it may contain duplicates.
The order of the list should be ascending by length of each word, and you
should return the list sorted by that rule.
If two words have the same length, sort the list alphabetically.
The function should return a list of strings in sorted order.
You may assume that all words will have the same length.
For example:
assert list_sort(["aa", "a", "aaa"]) => ["aa"]
assert list_sort(["ab", "a", "aaa", "cd"]) => ["ab", "cd"]
""" *)

Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Arith.PeanoNat.
Import ListNotations.

(* 任意字符串列表输入均可 *)
Definition Pre (input : list (list ascii)) : Prop := True.

Fixpoint lex_le (s1 s2 : list ascii) : bool :=
  match s1,s2 with
  | [], _ => true
  | _::_, [] => false
  | c1::t1, c2::t2 =>
    match Ascii.compare c1 c2 with
    | Lt => true | Gt => false | Eq => lex_le t1 t2
    end
  end.

Definition string_le (s1 s2 : list ascii) : bool :=
  match Nat.compare (length s1) (length s2) with
  | Lt => true | Gt => false | Eq => lex_le s1 s2
  end.

Definition has_even_length (s : list ascii) : bool := Nat.even (length s).

Fixpoint insert_by (le : list ascii -> list ascii -> bool) (x : list ascii) (l:list (list ascii)) : list (list ascii) :=
  match l with []=>[x] | h::t => if le x h then x::l else h::insert_by le x t end.
Fixpoint sort_by (le : list ascii -> list ascii -> bool) (l:list (list ascii)) : list (list ascii) :=
  match l with []=>[] | h::t => insert_by le h (sort_by le t) end.

Definition list_sort_impl (lst_in : list (list ascii)) : list (list ascii) :=
  sort_by string_le (filter has_even_length lst_in).

Definition sorted_list_sum_spec (input : list (list ascii)) (output : list (list ascii)) : Prop :=
  output = list_sort_impl input.
