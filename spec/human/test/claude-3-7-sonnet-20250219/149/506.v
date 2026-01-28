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
  problem_149_spec ["aaaa"; "bbb"; "ghij"; "ccc"; "dddd"; "ee"; "ffffff"; "worlld"]
                   ["ee"; "aaaa"; "dddd"; "ghij"; "ffffff"; "worlld"].
Proof.
  unfold problem_149_spec, list_sort_impl.
  simpl.
  (* filter has_even_length ["aaaa"; "bbb"; "ghij"; "ccc"; "dddd"; "ee"; "ffffff"; "worlld"] = *)
  (* filter on lengths: "aaaa"(4 even), "bbb"(3 odd), "ghij"(4 even), "ccc"(3 odd), "dddd"(4 even), "ee"(2 even), "ffffff"(6 even), "worlld"(6 even) *)
  (* result: ["aaaa"; "ghij"; "dddd"; "ee"; "ffffff"; "worlld"] *)

  (* sort_by string_le on ["aaaa"; "ghij"; "dddd"; "ee"; "ffffff"; "worlld"] *)
  (* sort by length ascending, then lex order for equal length *)
  (* lengths: ee(2), aaaa(4), ghij(4), dddd(4), ffffff(6), worlld(6) *)
  (* Within length 4: sort lex "aaaa", "dddd", "ghij" -> "aaaa" < "dddd" < "ghij" *)
  (* Within length 6: sort lex "ffffff", "worlld" -> "ffffff" < "worlld" *)
  (* Final sorted list: ["ee"; "aaaa"; "dddd"; "ghij"; "ffffff"; "worlld"] *)

  reflexivity.
Qed.