
Require Import List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  (forall p, In p factors -> prime p) /\
  (StrictlySorted Z.lt factors) \/ (exists i j, i < j /\ nth_error factors i = nth_error factors j) -> False) /\
  fold_left Z.mul factors 1 = n.
