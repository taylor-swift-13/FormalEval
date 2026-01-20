
Require Import Coq.Lists.List.
Import ListNotations.

Definition filter_integers_spec (values : list Type) (result : list nat) : Prop :=
  result = filter (fun x => match x with
                           | nat => true
                           | _ => false
                           end) values.
