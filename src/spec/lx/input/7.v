
(*  Filter an input list of strings only for ones that contain given substring
>>> filter_by_substring([], 'a')
[]
>>> filter_by_substring(['abc', 'bacd', 'cde', 'array'], 'a')
['abc', 'bacd', 'array']
 *)

(* ∀str, In(str, output) ↔ (In(str, strings) ∧ Contains(str, s)) 
  ∀i j ∈ [0,length(output)), ∃k l ∈ [0,length(intput)), input[k] = output[i] /\ input[l] = output[j] -> i < j -> k < l
  *)

Require Import List.
Require Import String.
Import ListNotations.

Open Scope string_scope.


(* 判断 s 是否包含子串 sub *)
Fixpoint contains_substring (s sub : string) : bool :=
  match s with
  | EmptyString => if sub =? EmptyString then true else false
  | String _ rest =>
      if String.prefix s sub then true
      else contains_substring rest sub
  end.

(*
  子列表定义
*)
Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : is_subsequence [] []
  | sub_cons_hd : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_tl : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).


Definition spec_filter_by_pre : Prop:= True.

Definition spec_filter_by_substring (input output : list string) (sub : string) : Prop:=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ contains_substring s sub = true)).
