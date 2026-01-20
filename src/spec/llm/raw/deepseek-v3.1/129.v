
Require Import List ZArith.
Import ListNotations.

Definition minPath_spec (grid : list (list Z)) (k : Z) (path : list Z) : Prop :=
  exists N x y mn,
    N = Z.of_nat (length grid) /\
    (forall i j, 0 <= i < N -> 0 <= j < N -> In (nth i grid [] !! j) (seq 1 (N * N))) /\
    (forall i, 0 <= i < N -> length (nth i grid []) = N) /\
    (exists i j, 0 <= i < N /\ 0 <= j < N /\ nth i grid [] !! j = Some 1 /\ x = i /\ y = j) /\
    (mn = fold_left Z.min 
      [if Z.ltb 0 x then nth (x - 1) grid [] !! y else None;
       if Z.ltb x (N - 1) then nth (x + 1) grid [] !! y else None;
       if Z.ltb 0 y then nth x grid [] !! (y - 1) else None;
       if Z.ltb y (N - 1) then nth x grid [] !! (y + 1) else None]
      (N * N + 1)) /\
    path = map (fun i => if Z.even i then 1 else mn) (seq 0 k).
