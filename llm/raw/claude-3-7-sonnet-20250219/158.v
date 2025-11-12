
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Program.Basics.

Open Scope string_scope.
Open Scope list_scope.

Fixpoint unique_chars (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c rest =>
    if in_dec Ascii.ascii_dec c (unique_chars rest) then unique_chars rest
    else c :: unique_chars rest
  end.

Definition unique_char_count (s : string) : nat :=
  length (unique_chars s).

Fixpoint lex_lt (a b : string) : Prop :=
  match a, b with
  | EmptyString, EmptyString => False
  | EmptyString, _ => True
  | _, EmptyString => False
  | String c1 s1', String c2 s2' =>
    (c1 < c2)%char \/ (c1 = c2 /\ lex_lt s1' s2')
  end.

Fixpoint find_max_spec (words : list string) (res : string) : Prop :=
  (res <> "" -> In res words) /\
  (forall w, In w words -> 
    unique_char_count w <= unique_char_count res) /\
  (forall w, In w words -> 
    unique_char_count w = unique_char_count res -> lex_lt res w \/ res = w).
