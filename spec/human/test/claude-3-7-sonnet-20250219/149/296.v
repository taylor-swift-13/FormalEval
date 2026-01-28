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
  problem_149_spec ["dbananaef"; "a"; "df"; "Python"; "ghij"; "kiwi"; "kiwi"] ["df"; "ghij"; "kiwi"; "kiwi"; "Python"].
Proof.
  unfold problem_149_spec, list_sort_impl.
  simpl.
  (* Filtered strings have even length: *)
  (* "dbananaef" length 9 (odd), excluded *)
  (* "a" length 1 (odd), excluded *)
  (* "df" length 2 (even), kept *)
  (* "Python" length 6 (even), kept *)
  (* "ghij" length 4 (even), kept *)
  (* "kiwi" length 4 (even), kept (twice) *)
  (* So filter has_even_length [...] = ["df"; "Python"; "ghij"; "kiwi"; "kiwi"] *)
  (* Now sort by string_le defined as length order, then lex order if lengths equal *)
  (* Lengths are: df(2), ghij(4), kiwi(4), kiwi(4), Python(6) *)
  (* So sorted order by length ascending: df, ghij, kiwi, kiwi, Python *)
  (* Among equal length strings with length 4: ghij vs kiwi lex compare *)
  (* "ghij" < "kiwi", so ghij precedes kiwi *)
  reflexivity.
Qed.