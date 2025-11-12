
Require Import List.
Require Import Arith.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Lists.ListSet.
Import ListNotations.

Definition unique_spec (l : list nat) (res : list nat) : Prop :=
  NoDup res /\
  (forall x, In x res <-> In x l) /\
  Sorted Nat.lt res.
