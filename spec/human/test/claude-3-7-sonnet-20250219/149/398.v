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
  problem_149_spec ["Helcccco"; "Programming"; "is"; "awesome"; "awesome"; "Programming"] ["is"; "Helcccco"].
Proof.
  unfold problem_149_spec, list_sort_impl.
  simpl.
  (* length "Helcccco" = 8 (even) -> kept *)
  (* length "Programming" = 11 (odd) -> filtered out *)
  (* length "is" = 2 (even) -> kept *)
  (* length "awesome" = 7 (odd) -> filtered out *)
  (* length "awesome" = 7 (odd) -> filtered out *)
  (* length "Programming" = 11 (odd) -> filtered out *)

  (* filter has_even_length input = ["Helcccco"; "is"] *)

  (* sort_by string_le ["Helcccco"; "is"] *)
  (* lengths: "Helcccco" = 8, "is" = 2 *)
  (* string_le compares length first: 2 < 8, so "is" < "Helcccco" *)

  (* After sorting, result = ["is"; "Helcccco"] *)

  reflexivity.
Qed.