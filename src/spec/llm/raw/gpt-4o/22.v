
Require Import List.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Definition is_integer (x : Any) : bool :=
  match x with
  | int _ => true
  | _ => false
  end.

Definition filter_integers_spec (values : list Any) (result : list int) : Prop :=
  result = filter (fun x => is_integer x) values.
