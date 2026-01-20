
Require Import Reals.
Require Import Lists.List.
Require Import Floats.
Open Scope R_scope.

Definition is_in_list (x : R) (l : list R) : Prop :=
  In x l.

Definition is_pair_from_list (a b : R) (l : list R) : Prop :=
  is_in_list a l /\ is_in_list b l.

Definition distance (a b : R) : R :=
  Rabs (a - b).

Definition is_closest_pair (a b : R) (l : list R) : Prop :=
  is_pair_from_list a b l /\
  a <> b \/ (exists i j, i <> j /\ nth_error l (Nat.pred (S i)) = Some a /\ nth_error l (Nat.pred (S j)) = Some b) /\
  a <= b /\
  (forall x y : R, is_pair_from_list x y l -> 
    (x <> y \/ (exists i j, i <> j /\ nth_error l (Nat.pred (S i)) = Some x /\ nth_error l (Nat.pred (S j)) = Some y)) ->
    distance a b <= distance x y).

Definition find_closest_elements_spec (numbers : list R) (result : R * R) : Prop :=
  length numbers >= 2 /\
  let (a, b) := result in
  is_pair_from_list a b numbers /\
  a <= b /\
  (forall x y : R, 
    is_pair_from_list x y numbers ->
    x <= y ->
    (x <> y \/ (exists i j : nat, i <> j /\ In x numbers /\ In y numbers)) ->
    distance a b <= distance x y).
