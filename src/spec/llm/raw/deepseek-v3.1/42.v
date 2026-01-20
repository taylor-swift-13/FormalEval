
Require Import List ZArith.
Import ListNotations.

Definition incr_list_spec (l : list Z) (result : list Z) : Prop :=
  result = map (fun x => x + 1) l.
