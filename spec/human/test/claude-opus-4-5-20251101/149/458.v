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

Definition str_apple : string := "apple"%string.
Definition str_banana : string := "banana"%string.
Definition str_lemmon : string := "lemmon"%string.
Definition str_cherry : string := "cherry"%string.
Definition str_datdddd : string := "datdddd"%string.
Definition str_grape : string := "grape"%string.
Definition str_kiwi : string := "kiwi"%string.
Definition str_lemon : string := "lemon"%string.

Example problem_149_test :
  problem_149_spec [str_apple; str_banana; str_lemmon; str_cherry; str_datdddd; str_grape; str_kiwi; str_lemon; str_cherry] [str_kiwi; str_banana; str_cherry; str_cherry; str_lemmon].
Proof.
  unfold problem_149_spec.
  unfold list_sort_impl.
  unfold str_apple, str_banana, str_lemmon, str_cherry, str_datdddd, str_grape, str_kiwi, str_lemon.
  simpl.
  reflexivity.
Qed.