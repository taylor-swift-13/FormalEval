Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Arith.PeanoNat.
Import ListNotations.

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

Example list_sort_impl_ex:
  list_sort_impl (("a"%char::"b"%char::nil)::("a"%char::nil)::("c"%char::"d"%char::nil)::nil)
  = (("a"%char::"b"%char::nil)::("c"%char::"d"%char::nil)::nil).
Proof. reflexivity. Qed.

Definition sorted_list_sum_spec (lst_in : list (list ascii)) (lst_out : list (list ascii)) : Prop :=
  lst_out = list_sort_impl lst_in.
