
Require Import List.
Require Import Bool.

Definition below_threshold_spec (l : list nat) (t : nat) (result : bool) : Prop :=
  result = forallb (fun x => x <? t) l.
