
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

Definition get_positive_spec (l : list nat) (result : list nat) : Prop :=
  result = filter (fun x => x > 0) l.
