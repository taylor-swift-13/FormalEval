
Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Lia.

Definition grid := list (list nat).

Definition in_bounds (N i j : nat) : Prop :=
  i < N /\ j < N.

Definition neighbors (N i j x y : nat) : Prop :=
  in_bounds N i j /\
  in_bounds N x y /\
  ((x = i /\ (y = j + 1 \/ (1 <= y /\ y + 1 = j))) \/
   (y = j /\ (x = i + 1 \/ (1 <= x /\ x + 1 = i)))).

Definition unique_values_grid (N : nat) (g : grid) : Prop :=
  length g = N /\
  Forall (fun row => length row = N) g /\
  (forall v, 1 <= v <= N * N -> 
     exists i j, i < N /\ j < N /\ nth_error g i = Some (nth j (nth i g []) 0) /\ nth j (nth i g []) 0 = v) /\
  (* each value appears exactly once *)
  (forall v i1 j1 i2 j2,
      i1 < N -> j1 < N -> i2 < N -> j2 < N ->
      nth_error g i1 = Some (nth j1 (nth i1 g []) 0) ->
      nth_error g i2 = Some (nth j2 (nth i2 g []) 0) ->
      nth j1 (nth i1 g []) 0 = v ->
      nth j2 (nth i2 g []) 0 = v ->
      (i1, j1) = (i2, j2)).

Definition min_val_adjacent (N : nat) (g : grid) (x y mn : nat) : Prop :=
  (* mn is minimum among values on neighbors of cell (x,y) if they exist, or N * N if none *)
  in_bounds N x y /\
  let vals := 
    (if x > 0 then [nth y (nth (x - 1) g []) (N*N)] else []) ++
    (if x < N - 1 then [nth y (nth (x + 1) g []) (N*N)] else []) ++
    (if y > 0 then [nth (y - 1) (nth x g []) (N*N)] else []) ++
    (if y < N - 1 then [nth (y + 1) (nth x g []) (N*N)] else []) in
  mn = fold_left Nat.min vals (N*N).

Definition minPath_spec (g : grid) (k : nat) (res : list nat) : Prop :=
  exists N x y mn,
    N = length g /\
    N >= 2 /\
    unique_values_grid N g /\
    (* (x,y) is position of value 1 in g *)
    in_bounds N x y /\
    nth y (nth x g []) 0 = 1 /\
    min_val_adjacent N g x y mn /\
    length res = k /\
    (forall i, i < k ->
       nth i res 0 = if Nat.even i then 1 else mn).
