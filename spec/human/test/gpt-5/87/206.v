Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope Z_scope.

Inductive coord_order (c1 c2 : Z * Z) : Prop :=
  | row_lt : fst c1 < fst c2 -> coord_order c1 c2
  | col_gt : fst c1 = fst c2 -> snd c1 > snd c2 -> coord_order c1 c2.

Fixpoint is_sorted (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | c1 :: (c2 :: _ as tail) => coord_order c1 c2 /\ is_sorted tail
  end.

Inductive Cell :=
  | Zc : Z -> Cell
  | Sc : string -> Cell.

Fixpoint collect_coords_row (row : list Cell) (r c : Z) (x : Z) : list (Z * Z) :=
  match row with
  | [] => []
  | h :: t =>
      match h with
      | Zc hZ =>
          if Z.eqb hZ x then
            (r, c) :: collect_coords_row t r (Z.succ c) x
          else
            collect_coords_row t r (Z.succ c) x
      | Sc _ =>
          collect_coords_row t r (Z.succ c) x
      end
  end.

Fixpoint collect_all_coords (lst : list (list Cell)) (r : Z) (x : Z) : list (Z * Z) :=
  match lst with
  | [] => []
  | row :: rest =>
      collect_coords_row row r 0 x ++ collect_all_coords rest (Z.succ r) x
  end.

Fixpoint insert_coord (coord : Z * Z) (coords : list (Z * Z)) : list (Z * Z) :=
  match coords with
  | [] => [coord]
  | h :: t =>
      if Z.ltb (fst coord) (fst h) then
        coord :: coords
      else if Z.eqb (fst coord) (fst h) then
        if Z.ltb (snd h) (snd coord) then
          coord :: coords
        else
          h :: insert_coord coord t
      else
        h :: insert_coord coord t
  end.

Fixpoint sort_coords (coords : list (Z * Z)) : list (Z * Z) :=
  match coords with
  | [] => []
  | h :: t => insert_coord h (sort_coords t)
  end.

Definition get_row_impl (lst : list (list Cell)) (x : Z) : list (Z * Z) :=
  sort_coords (collect_all_coords lst 0 x).

Definition problem_87_pre (lst : list (list Cell)) (x : Z) : Prop := True.

Definition problem_87_spec (lst : list (list Cell)) (x : Z) (res : list (Z * Z)) : Prop :=
  res = get_row_impl lst x.

Example problem_87_example :
  problem_87_spec
    [[Zc 1%Z];
     [Zc 1%Z];
     [Sc "Qmiom"%string; Sc "OXMYkjFnn"%string; Sc "zxopRHtsCb"%string; Sc "SPOKvaykqJ"%string; Sc "ihaVTyy"%string; Sc "OCr"%string; Sc "yP"%string; Sc "nCIHYIJiq"%string];
     [];
     [Zc 1%Z]]
    (-1%Z)
    [].
Proof.
  unfold problem_87_spec, get_row_impl.
  vm_compute.
  reflexivity.
Qed.