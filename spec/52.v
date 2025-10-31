Require Import Coq.Lists.List.
Import ListNotations.

Definition below_threshold_spec (l : list nat) (t : nat) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).