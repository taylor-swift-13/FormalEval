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
  problem_149_spec ["Hello"; "woorld"; "Programming"; "is"; "klmno"; "nklmno"; "Python"; "Programming"; "Hello"; "is"; "nklmno"]
                   ["is"; "is"; "Python"; "nklmno"; "nklmno"; "woorld"].
Proof.
  unfold problem_149_spec, list_sort_impl.
  simpl.
  (* Filter only even length strings:
     "Hello" (5, odd) no
     "woorld" (6, even) yes
     "Programming" (11, odd) no
     "is" (2, even) yes
     "klmno" (5, odd) no
     "nklmno" (6, even) yes
     "Python" (6, even) yes
     "Programming" (11, odd) no
     "Hello" (5, odd) no
     "is" (2, even) yes
     "nklmno" (6, even) yes

     After filter: ["woorld"; "is"; "nklmno"; "Python"; "is"; "nklmno"]
  *)

  (* Sort by length then lex:
     Lengths: is (2), is (2), Python(6), nklmno(6), nklmno(6), woorld(6)

     Among length 2: "is" and "is" sorted lex = ["is"; "is"]
     Among length 6: "Python", "nklmno", "nklmno", "woorld"

     length equal so lex order:
       "Python" vs "nklmno"
       Compare first char 'P' (80) vs 'n' (110)
       'P' < 'n' so Python < nklmno

       "Python" < "nklmno"

       Compare "nklmno" and "woorld":
       'n' (110) < 'w' (119) so nklmno < woorld

     Overall length-6 strings sorted lex: ["Python"; "nklmno"; "nklmno"; "woorld"]

     Final sorted list: ["is"; "is"; "Python"; "nklmno"; "nklmno"; "woorld"]
  *)

  reflexivity.
Qed.