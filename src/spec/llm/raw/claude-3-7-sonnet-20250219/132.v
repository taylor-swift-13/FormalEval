
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

Fixpoint max (a b : nat) : nat :=
  if a <? b then b else a.

Fixpoint max_nested_depth (l : list ascii) (start end_ : nat) : option nat :=
  let fix aux i cnt max_nest :=
    match nth_error l i with
    | None => None
    | Some c =>
      if i >? end_ then None else
      let cnt' := if c =? "["%char then S cnt else pred cnt in
      if cnt' =? 0 then Some (max max_nest (S cnt))
      else aux (S i) cnt' (max max_nest (S cnt))
    end
  in aux start 0 0.

Fixpoint valid_subseq_nested (l : list ascii) : bool :=
  let fix loop i :=
    match nth_error l i with
    | None => false
    | Some c =>
      if c =? "]"%char then loop (S i) else
      match max_nested_depth l i (length l - 1) with
      | Some d => if d >=? 2 then true else loop (S i)
      | None => false
      end
    end
  in loop 0.

Definition is_nested_spec (s : string) (res : bool) : Prop :=
  res = valid_subseq_nested (list_ascii_of_string s).
