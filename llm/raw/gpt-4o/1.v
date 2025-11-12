
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition separate_paren_groups_spec (paren_string : string) (results : list string) : Prop :=
  forall group,
    In group results <->
    exists start end,
      substring start (end - start + 1) paren_string = group /\
      (forall i, start <= i <= end -> nth i paren_string " " <> " ") /\
      (forall i, start <= i <= end -> nth i paren_string " " = "(" -> exists j, i < j <= end /\ nth j paren_string " " = ")") /\
      (forall i, start <= i <= end -> nth i paren_string " " = ")" -> exists j, start <= j < i /\ nth j paren_string " " = "(") /\
      (forall i, start <= i <= end -> nth i paren_string " " <> "(" -> nth i paren_string " " <> ")") /\
      (forall i j, start <= i < j <= end -> nth i paren_string " " = "(" -> nth j paren_string " " = ")" -> forall k, i < k < j -> nth k paren_string " " <> "(" /\ nth k paren_string " " <> ")").
