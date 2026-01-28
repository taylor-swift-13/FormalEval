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
  problem_149_spec ["Hello"; "world"; "Programming"; "isProgra"; "klmno"; "sttu"; ""; "date"; "Python"; "Programming"; "world"; "Python"; "klmno"]
                   [""; "date"; "sttu"; "Python"; "Python"; "isProgra"].
Proof.
  unfold problem_149_spec, list_sort_impl.
  simpl.

  (* Filter with has_even_length: keep strings of even length *)
  (* Lengths:
     "Hello" = 5 (odd)
     "world" = 5 (odd)
     "Programming" = 11 (odd)
     "isProgra" = 8 (even)
     "klmno" = 5 (odd)
     "sttu" = 4 (even)
     "" = 0 (even)
     "date" = 4 (even)
     "Python" = 6 (even)
     "Programming" = 11 (odd)
     "world" = 5 (odd)
     "Python" = 6 (even)
     "klmno" = 5 (odd)
     So filtered list: ["isProgra"; "sttu"; ""; "date"; "Python"; "Python"]

  Sorting by length and lex order:
  Lengths in ascending order:
    "" (0)
    "date" (4)
    "sttu" (4)
    "Python" (6)
    "Python" (6)
    "isProgra" (8)

  For same length, lex order between "date" and "sttu":
    "date" < "sttu"
  For same length, lex order between "Python" and "Python" same strings
  Entire sorted list:
    ["", "date", "sttu", "Python", "Python", "isProgra"]

  So output matches expectation.
*)

  reflexivity.
Qed.