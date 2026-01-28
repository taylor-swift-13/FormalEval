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

Definition str_this : string := "this"%string.
Definition str_list : string := "list"%string.
Definition str_halevels : string := "halevels"%string.
Definition str_words : string := "words"%string.
Definition str_of : string := "of"%string.
Definition str_different : string := "different"%string.
Definition str_lengths : string := "lengths"%string.

Example problem_149_test :
  problem_149_spec [str_this; str_list; str_halevels; str_words; str_of; str_different; str_lengths] [str_of; str_list; str_this; str_halevels].
Proof.
  unfold problem_149_spec.
  unfold list_sort_impl.
  unfold str_this, str_list, str_halevels, str_words, str_of, str_different, str_lengths.
  simpl.
  reflexivity.
Qed.