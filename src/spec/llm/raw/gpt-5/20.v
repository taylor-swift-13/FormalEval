Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope R_scope.

Definition occurs_twice (x : R) (l : list R) : Prop :=
  exists l1 l2 l3, l = l1 ++ x :: l2 ++ x :: l3.

Definition pair_from_list (l : list R) (x y : R) : Prop :=
  (x < y /\ In x l /\ In y l) \/ (x = y /\ occurs_twice x l).

Definition find_closest_elements_spec (numbers : list R) (res : R * R) : Prop :=
  2 <= length numbers /\
  let '(a, b) := res in
  a <= b /\
  pair_from_list numbers a b /\
  forall x y, pair_from_list numbers x y -> b - a <= y - x.