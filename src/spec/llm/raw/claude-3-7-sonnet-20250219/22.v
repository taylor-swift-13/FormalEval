
Require Import List.
Import ListNotations.

Definition filter_integers_spec (values : list {x : Type & x}) (result : list Z) : Prop :=
  (* "values" is a list of dynamically typed values packed with their type information.
     "result" is a list of integers (Z) extracted from "values". *)
  (* The result contains exactly those elements of "values" whose type is int, projected to Z. *)
  result = map
             (fun x => projT2 x)
             (filter (fun x => match x with
                               | existT _ t v => if (type_eq_dec t int) then true else false
                               end)
                     values).
