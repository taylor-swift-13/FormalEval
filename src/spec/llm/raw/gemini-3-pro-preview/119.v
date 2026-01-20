
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.
Open Scope char_scope.

Fixpoint valid_parens_aux (l : list ascii) (cnt : Z) : bool :=
  match l with
  | [] => cnt =? 0
  | c :: rest =>
      let new_cnt := if (c =? "(") then cnt + 1 else cnt - 1 in
      if new_cnt <? 0 then false 
      else valid_parens_aux rest new_cnt
  end.

Definition valid_parens (s : string) : bool :=
  valid_parens_aux (list_ascii_of_string s) 0.

Definition match_parens_spec (lst : list string) (res : string) : Prop :=
  match lst with
  | s1 :: s2 :: nil =>
      let check := valid_parens (s1 ++ s2) || valid_parens (s2 ++ s1) in
      res = if check then "Yes" else "No"
  | _ => False
  end.
