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
  problem_149_spec ["cccc"; "ddd"; "e"; "zzzz"; "yy"; "ddddat"; "xxxxx"; "rrrrrr"; "sssssss"; "xxxxx"]
                   ["yy"; "cccc"; "zzzz"; "ddddat"; "rrrrrr"].
Proof.
  unfold problem_149_spec, list_sort_impl.
  simpl.
  (* Filtered list with even length strings *)
  (* "cccc" length 4 (even): keep *)
  (* "ddd" length 3 (odd): remove *)
  (* "e" length 1 (odd): remove *)
  (* "zzzz" length 4 (even): keep *)
  (* "yy" length 2 (even): keep *)
  (* "ddddat" length 6 (even): keep *)
  (* "xxxxx" length 5 (odd): remove *)
  (* "rrrrrr" length 6 (even): keep *)
  (* "sssssss" length 7 (odd): remove *)
  (* "xxxxx" length 5 (odd): remove *)
  (* So filtered list = ["cccc"; "zzzz"; "yy"; "ddddat"; "rrrrrr"] *)

  (* Now sort_by string_le this filtered list *)

  (* Sort order by length, then lex order: lengths are 2 ("yy"), 4 ("cccc","zzzz"), 6 ("ddddat","rrrrrr") *)

  (* Among length 2: ["yy"] *)
  (* Among length 4: sort lex "cccc", "zzzz" -> "cccc" < "zzzz" *)
  (* Among length 6: "ddddat" < "rrrrrr" lex *)

  (* Final sorted list: ["yy"; "cccc"; "zzzz"; "ddddat"; "rrrrrr"] *)

  reflexivity.
Qed.