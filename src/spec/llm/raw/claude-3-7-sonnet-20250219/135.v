
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition can_arrange_spec (arr : list Z) (idx : Z) : Prop :=
  (exists i : nat, 
      i < length arr /\
      i > 0 /\
      Z.of_nat i = idx /\
      nth i arr 0 < nth (i - 1) arr 0 /\
      (forall j : nat, j < length arr -> j > 0 -> j > i -> nth j arr 0 >= nth (j - 1) arr 0))
  \/ (idx = -1 /\ forall i : nat, i < length arr -> i > 0 -> nth i arr 0 >= nth (i - 1) arr 0).
