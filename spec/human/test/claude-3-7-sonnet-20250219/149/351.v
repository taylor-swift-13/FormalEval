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
  problem_149_spec ["apple"; "sssssss"; "bb"; "banana"; "cherry"; "date"; "grape"; "lemonn"; "banana"; "lemonn"]
                   ["bb"; "date"; "banana"; "banana"; "cherry"; "lemonn"; "lemonn"].
Proof.
  unfold problem_149_spec, list_sort_impl.
  simpl.
  (* filter has_even_length removes strings with odd length: *)
  (* "apple" (5), "sssssss" (7), "grape" (5) are filtered out *)
  (* remaining: ["bb"; "banana"; "cherry"; "date"; "lemonn"; "banana"; "lemonn"] *)
  (* sort_by string_le sorts by length then lex order: lengths: *)
  (* "bb" (2), "date" (4), "banana" (6), "banana" (6), "cherry" (6), "lemonn" (6), "lemonn" (6) *)
  (* among length 6: "banana" < "cherry" < "lemonn" lex order *)
  reflexivity.
Qed.