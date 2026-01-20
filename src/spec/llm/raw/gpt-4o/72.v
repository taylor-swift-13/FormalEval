
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Definition will_it_fly_spec (q : list nat) (w : nat) (result : bool) : Prop :=
  result = (andb (q =? rev q) (sum q <=? w)).
