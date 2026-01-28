Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* Definition of sorting relation:
   - Ascending by row (r).
   - Descending by column (c) if rows are equal.
*)
Inductive coord_order (c1 c2 : Z * Z) : Prop :=
  | row_lt : fst c1 < fst c2 -> coord_order c1 c2
  | col_gt : fst c1 = fst c2 -> snd c1 > snd c2 -> coord_order c1 c2.

(* Check if a list of coordinates is sorted according to coord_order. *)
Fixpoint is_sorted (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | c1 :: (c2 :: _ as tail) => coord_order c1 c2 /\ is_sorted tail
  end.

(* Collect coordinates from a single row matching x *)
Fixpoint collect_coords_row (row : list Z) (r c : Z) (x : Z) : list (Z * Z) :=
  match row with
  | [] => []
  | h :: t =>
      if Z.eqb h x then
        (r, c) :: collect_coords_row t r (Z.succ c) x
      else
        collect_coords_row t r (Z.succ c) x
  end.

(* Collect all coordinates from the nested list matching x *)
Fixpoint collect_all_coords (lst : list (list Z)) (r : Z) (x : Z) : list (Z * Z) :=
  match lst with
  | [] => []
  | row :: rest =>
      collect_coords_row row r 0 x ++ collect_all_coords rest (Z.succ r) x
  end.

(* Insert a coordinate into a sorted list maintaining the order *)
Fixpoint insert_coord (coord : Z * Z) (coords : list (Z * Z)) : list (Z * Z) :=
  match coords with
  | [] => [coord]
  | h :: t =>
      if Z.ltb (fst coord) (fst h) then
        coord :: coords
      else if Z.eqb (fst coord) (fst h) then
        (* For same row, we want descending column order.
           If coord.col > h.col, coord should come before h. *)
        if Z.ltb (snd h) (snd coord) then
          coord :: coords
        else
          h :: insert_coord coord t
      else
        h :: insert_coord coord t
  end.

(* Sort the list of coordinates using insertion sort *)
Fixpoint sort_coords (coords : list (Z * Z)) : list (Z * Z) :=
  match coords with
  | [] => []
  | h :: t => insert_coord h (sort_coords t)
  end.

(* Main implementation *)
Definition get_row_impl (lst : list (list Z)) (x : Z) : list (Z * Z) :=
  sort_coords (collect_all_coords lst 0 x).

Definition problem_87_pre (lst : list (list Z)) (x : Z) : Prop := True.

Definition problem_87_spec (lst : list (list Z)) (x : Z) (res : list (Z * Z)) : Prop :=
  res = get_row_impl lst x.

Example test_case_problem_87:
  problem_87_spec
    [[1; 2]; [2; 3; 4]; [4; 5; 6; 7]; [7; 8; 9; 10; 11]]
    4
    [(1, 2); (2, 0)].
Proof.
  unfold problem_87_spec.
  unfold get_row_impl.
  vm_compute.
  reflexivity.
Qed.