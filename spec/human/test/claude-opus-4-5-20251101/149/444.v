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

Definition str_a : string := String "a" EmptyString.
Definition str_b : string := String "b" EmptyString.
Definition str_bc : string := String "b" (String "c" EmptyString).
Definition str_def : string := String "d" (String "e" (String "f" EmptyString)).
Definition str_jjisklmno : string := String "j" (String "j" (String "i" (String "s" (String "k" (String "l" (String "m" (String "n" (String "o" EmptyString)))))))).
Definition str_bbc : string := String "b" (String "b" (String "c" EmptyString)).
Definition str_aa : string := String "a" (String "a" EmptyString).
Definition str_klmno : string := String "k" (String "l" (String "m" (String "n" (String "o" EmptyString)))).
Definition str_xxxxx : string := String "x" (String "x" (String "x" (String "x" (String "x" EmptyString)))).

Example problem_149_test :
  problem_149_spec [str_a; str_b; str_bc; str_def; str_jjisklmno; str_bbc; str_aa; str_klmno; str_xxxxx] [str_aa; str_bc].
Proof.
  unfold problem_149_spec.
  unfold list_sort_impl.
  unfold str_a, str_b, str_bc, str_def, str_jjisklmno, str_bbc, str_aa, str_klmno, str_xxxxx.
  simpl.
  reflexivity.
Qed.