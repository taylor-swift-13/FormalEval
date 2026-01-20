
Require Import List.
Require Import ZArith.
Require Import Sorting.
Require Import Orders.

Definition get_row_spec (lst : list (list Z)) (x : Z) (result : list (Z * Z)) : Prop :=
  (forall i j, In (i, j) result -> (i < length lst)%Z /\ (j < length (nth i lst nil))%Z /\ nth j (nth i lst nil) 0 = x) /\
  (forall i l, In i (seq 0 (length lst)) -> In j (seq 0 (length (nth i lst nil))) -> nth j (nth i lst nil) 0 = x -> In (i, j) result) /\
  Sorted (fun a b => fst a < fst b \/ (fst a = fst b /\ snd b < snd a)) result.
