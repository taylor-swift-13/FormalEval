
Require Import List.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.

Definition get_row_spec (lst : list (list nat)) (x : nat) (res : list (nat * nat)) : Prop :=
  forall i j,
    (In (i, j) res <->
      (i < length lst /\
       j < length (nth i lst []) /\
       nth j (nth i lst []) 0 = x)) /\
  (forall i1 j1 i2 j2,
    In (i1, j1) res ->
    In (i2, j2) res ->
    (i1 < i2 \/ (i1 = i2 /\ j1 > j2))).
