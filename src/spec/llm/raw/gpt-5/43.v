Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.

Open Scope Z_scope.

Definition pairs_sum_to_zero_spec (l : list Z) (res : bool) : Prop :=
  (res = true <-> exists i j : nat,
      i <> j /\ i < length l /\ j < length l /\ nth i l 0%Z + nth j l 0%Z = 0%Z)
  /\ (res = false <-> forall i j : nat,
      i <> j -> i < length l -> j < length l -> nth i l 0%Z + nth j l 0%Z <> 0%Z).