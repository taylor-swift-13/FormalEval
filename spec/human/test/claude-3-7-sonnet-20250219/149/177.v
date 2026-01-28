Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat.
Import ListNotations.

Open Scope string_scope.

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

Example test_case_149 :
  problem_149_spec 
    ["Hello"; "woorld"; "Programming"; "is"; "klmno"; "nklmno"; "Python"; "Programming"; "Hello"] 
    ["is"; "Python"; "nklmno"; "woorld"].
Proof.
  unfold problem_149_spec, list_sort_impl.
  simpl.
  (* filter has_even_length
     "Hello" length 5 odd -> removed
     "woorld" length 6 even -> kept
     "Programming" length 11 odd -> removed
     "is" length 2 even -> kept
     "klmno" length 5 odd -> removed
     "nklmno" length 6 even -> kept
     "Python" length 6 even -> kept
     "Programming" length 11 odd -> removed
     "Hello" length 5 odd -> removed
     So filtered list = ["woorld"; "is"; "nklmno"; "Python"]
  *)

  (* sort_by string_le sorts by length ascending, then lex order *)

  (* Their lengths:
    "is" = 2
    "woorld" = 6
    "nklmno" = 6
    "Python" = 6
  *)

  (* Length 2 "is" first *)

  (* Among length 6 strings: compare lex order
     lex_le "Python" "woorld" ?
       'P' = 80, 'w' = 119
       80 < 119, so "Python" < "woorld"

     lex_le "nklmno" "Python" ?
       'n' = 110, 'P' = 80
       110 > 80, so "nklmno" > "Python"

     So order among length 6 strings is "Python" < "nklmno" < "woorld"

  *)

  (* So sorted = ["is"; "Python"; "nklmno"; "woorld"] *)

  reflexivity.
Qed.