（* def below_threshold(l: list, t: int):
"""Return True if all numbers in the list l are below threshold t.
>>> below_threshold([1, 2, 4, 10], 100)
True
>>> below_threshold([1, 20, 4, 10], 5)
False
""" *）
Require Import Coq.Lists.List.
Import ListNotations.

(* Pre: no special constraints for `below_threshold` *)
Definition Pre (l : list nat) : Prop := True.

Definition below_threshold_spec (l : list nat) (t : nat) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).