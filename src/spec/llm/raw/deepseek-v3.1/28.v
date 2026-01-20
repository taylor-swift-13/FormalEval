
Require Import List String.
Import ListNotations.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_left append strings "".
