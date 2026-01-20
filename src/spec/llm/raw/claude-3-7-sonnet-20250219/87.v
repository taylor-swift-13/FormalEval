
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

Definition index := nat.
Definition coordinate := (index * index)%type.

Fixpoint get_row_spec (lst : list (list nat)) (x : nat) (res : list coordinate) : Prop :=
  (* res contains exactly the coordinates (i,j) where lst[i][j] = x *)
  (forall i j,
      nth_error lst i = Some (nth j (nth i lst [] []) 0) ->
      nth j (nth i lst [] []) = x ->
      In (i,j) res) /\
  (forall (c : coordinate),
      In c res ->
      let (i,j) := c in
      nth_error lst i <> None /\
      nth_error (nth i lst [] []) j = Some x) /\
  (* For each row, coordinates with that row index appear in res ordered by descending column index *)
  (forall i,
      let row := nth i lst [] in
      let coords_in_row := filter (fun c => fst c =? i) res in
      forall k1 k2,
        nth_error coords_in_row k1 = Some (i,j1) ->
        nth_error coords_in_row k2 = Some (i,j2) ->
        k1 < k2 -> j1 > j2) /\
  (* Coordinates in res are sorted by ascending row index (i) *)
  (forall k1 k2,
      nth_error res k1 = Some (i1,j1) ->
      nth_error res k2 = Some (i2,j2) ->
      k1 < k2 -> i1 <= i2).
