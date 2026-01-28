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
  problem_149_spec ["a"; "bc"; "def"; "ghij"; "klmno"; "p"; "qr"; "stu"; "vwxy"; "vwxy"]
                   ["bc"; "qr"; "ghij"; "vwxy"; "vwxy"].
Proof.
  unfold problem_149_spec, list_sort_impl.
  simpl.
  (* filter has_even_length removes strings with length odd:
     "a"(1), "def"(3), "klmno"(5), "p"(1), "stu"(3) removed
     Remaining: ["bc"(2); "ghij"(4); "qr"(2); "vwxy"(4); "vwxy"(4)] *)

  (* sort_by string_le sorts by length ascending, then lex order *)
  (* Lengths: bc(2), qr(2), ghij(4), vwxy(4), vwxy(4) *)
  (* For length 2: "bc" < "qr" lex *)
  (* For length 4: "ghij" < "vwxy" lex *)
  reflexivity.
Qed.