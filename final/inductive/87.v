(* def get_row(lst, x):
"""
You are given a 2 dimensional data, as a nested lists,
which is similar to matrix, however, unlike matrices,
each row may contain a different number of columns.
Given lst, and integer x, find integers x in the list,
and return list of tuples, [(x1, y1), (x2, y2) ...] such that
each tuple is a coordinate - (row, columns), starting with 0.
Sort coordinates initially by rows in ascending order.
Also, sort coordinates of the row by columns in descending order.

Examples:
get_row([
[1,2,3,4,5,6],
[1,2,3,4,1,6],
[1,2,3,4,5,1]
], 1) == [(0, 0), (1, 4), (1, 0), (2, 5), (2, 0)]
get_row([], 1) == []
get_row([[], [1], [1, 2, 3]], 3) == [(2, 2)]
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition get_elem {A : Type} (lst : list (list A)) (coord : nat * nat) : option A :=
  match nth_error lst (fst coord) with
  | Some row => nth_error row (snd coord)
  | None => None
  end.

Inductive coord_order_rel : nat * nat -> nat * nat -> Prop :=
  | cor_row_lt : forall c1 c2, fst c1 < fst c2 -> coord_order_rel c1 c2
  | cor_col_gt : forall c1 c2, fst c1 = fst c2 -> snd c1 > snd c2 -> coord_order_rel c1 c2.

Inductive is_sorted_rel : list (nat * nat) -> Prop :=
  | isr_nil : is_sorted_rel []
  | isr_single : forall c, is_sorted_rel [c]
  | isr_cons : forall c1 c2 tail,
      coord_order_rel c1 c2 ->
      is_sorted_rel (c2 :: tail) ->
      is_sorted_rel (c1 :: c2 :: tail).

Inductive collect_coords_row_rel : list nat -> nat -> nat -> nat -> list (nat * nat) -> Prop :=
  | ccrr_nil : forall r c x, collect_coords_row_rel [] r c x []
  | ccrr_match : forall h t r c x result,
      Nat.eqb h x = true ->
      collect_coords_row_rel t r (S c) x result ->
      collect_coords_row_rel (h :: t) r c x ((r, c) :: result)
  | ccrr_no_match : forall h t r c x result,
      Nat.eqb h x = false ->
      collect_coords_row_rel t r (S c) x result ->
      collect_coords_row_rel (h :: t) r c x result.

Inductive collect_all_coords_rel : list (list nat) -> nat -> nat -> list (nat * nat) -> Prop :=
  | cacr_nil : forall r x, collect_all_coords_rel [] r x []
  | cacr_cons : forall row rest r x row_coords rest_coords,
      collect_coords_row_rel row r 0 x row_coords ->
      collect_all_coords_rel rest (S r) x rest_coords ->
      collect_all_coords_rel (row :: rest) r x (row_coords ++ rest_coords).

Inductive insert_coord_rel : nat * nat -> list (nat * nat) -> list (nat * nat) -> Prop :=
  | icr_nil : forall coord, insert_coord_rel coord [] [coord]
  | icr_row_lt : forall coord h t,
      (fst coord < fst h) ->
      insert_coord_rel coord (h :: t) (coord :: h :: t)
  | icr_row_eq_col_gt : forall coord h t,
      (fst coord = fst h) ->
      (snd h < snd coord) ->
      insert_coord_rel coord (h :: t) (coord :: h :: t)
  | icr_skip : forall coord h t result,
      ((fst coord > fst h) \/ (fst coord = fst h /\ snd h >= snd coord)) ->
      insert_coord_rel coord t result ->
      insert_coord_rel coord (h :: t) (h :: result).

Inductive sort_coords_rel : list (nat * nat) -> list (nat * nat) -> Prop :=
  | scr_nil : sort_coords_rel [] []
  | scr_cons : forall h t sorted_tail result,
      sort_coords_rel t sorted_tail ->
      insert_coord_rel h sorted_tail result ->
      sort_coords_rel (h :: t) result.


Definition get_row_spec (lst : list (list nat)) (x : nat) (res : list (nat * nat)) : Prop :=
  exists coords,
    collect_all_coords_rel lst 0 x coords /\
    sort_coords_rel coords res.
