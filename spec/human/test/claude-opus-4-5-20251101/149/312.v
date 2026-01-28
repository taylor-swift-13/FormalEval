Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat.
Import ListNotations.

Fixpoint lex_le (s1 s2 : string) : bool :=
  match s1,s2 with
  | EmptyString, _ => true
  | String _ _, EmptyString => false
  | String c1 t1, String c2 t2 =>
    match Ascii.compare c1 c2 with
    | Lt => true | Gt => false | Eq => lex_le t1 t2
    end
  end.

Definition string_le (s1 s2 : string) : bool :=
  match Nat.compare (length s1) (length s2) with
  | Lt => true | Gt => false | Eq => lex_le s1 s2
  end.

Definition has_even_length (s : string) : bool := Nat.even (length s).

Fixpoint insert_by (le : string -> string -> bool) (x : string) (l:list string) : list string :=
  match l with []=>[x] | h::t => if le x h then x::l else h::insert_by le x t end.
Fixpoint sort_by (le : string -> string -> bool) (l:list string) : list string :=
  match l with []=>[] | h::t => insert_by le h (sort_by le t) end.

Definition list_sort_impl (lst_in : list string) : list string :=
  sort_by string_le (filter has_even_length lst_in).

Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  output = list_sort_impl input.

Definition str_cccc : string := String "c" (String "c" (String "c" (String "c" EmptyString))).
Definition str_ddd : string := String "d" (String "d" (String "d" EmptyString)).
Definition str_ee : string := String "e" (String "e" EmptyString).
Definition str_zzzz : string := String "z" (String "z" (String "z" (String "z" EmptyString))).
Definition str_yy : string := String "y" (String "y" EmptyString).
Definition str_xxxxxx : string := String "x" (String "x" (String "x" (String "x" (String "x" (String "x" EmptyString))))).
Definition str_rrrrrr : string := String "r" (String "r" (String "r" (String "r" (String "r" (String "r" EmptyString))))).
Definition str_sssssss : string := String "s" (String "s" (String "s" (String "s" (String "s" (String "s" (String "s" EmptyString)))))).
Definition str_eee : string := String "e" (String "e" (String "e" EmptyString)).

Example problem_149_test :
  problem_149_spec [str_cccc; str_ddd; str_ee; str_zzzz; str_yy; str_xxxxxx; str_rrrrrr; str_sssssss; str_yy; str_eee; str_yy] [str_ee; str_yy; str_yy; str_yy; str_cccc; str_zzzz; str_rrrrrr; str_xxxxxx].
Proof.
  unfold problem_149_spec.
  unfold list_sort_impl.
  unfold str_cccc, str_ddd, str_ee, str_zzzz, str_yy, str_xxxxxx, str_rrrrrr, str_sssssss, str_eee.
  simpl.
  reflexivity.
Qed.