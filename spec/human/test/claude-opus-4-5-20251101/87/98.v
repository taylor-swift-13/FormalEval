Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(*
 * 排序关系定义：
 * - 首先按行号 (r) 升序。
 * - 如果行号相同，则按列号 (c) 降序。
 *)
Inductive coord_order (c1 c2 : Z * Z) : Prop :=
  | row_lt : fst c1 < fst c2 -> coord_order c1 c2
  | col_gt : fst c1 = fst c2 -> snd c1 > snd c2 -> coord_order c1 c2.

(*
 * 检查一个坐标列表是否根据 coord_order 关系进行了排序。
 * 这个版本可以通过 Coq 的终止性检查。
 *)
Fixpoint is_sorted (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | c1 :: (c2 :: _ as tail) => coord_order c1 c2 /\ is_sorted tail
  end.

Fixpoint collect_coords_row (row : list Z) (r c : Z) (x : Z) : list (Z * Z) :=
  match row with
  | [] => []
  | h :: t =>
      if Z.eqb h x then
        (r, c) :: collect_coords_row t r (Z.succ c) x
      else
        collect_coords_row t r (Z.succ c) x
  end.

Fixpoint collect_all_coords (lst : list (list Z)) (r : Z) (x : Z) : list (Z * Z) :=
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

Definition get_row_impl (lst : list (list Z)) (x : Z) : list (Z * Z) :=
  sort_coords (collect_all_coords lst 0 x).

Definition problem_87_pre (lst : list (list Z)) (x : Z) : Prop := True.

Definition problem_87_spec (lst : list (list Z)) (x : Z) (res : list (Z * Z)) : Prop :=
  res = get_row_impl lst x.

Example test_get_row_2 :
  problem_87_spec 
    [[1%Z; 5%Z; 3%Z; 5%Z; (-66)%Z; 5%Z; 9%Z; 5%Z; 11%Z; 5%Z; 13%Z; 5%Z]] 
    5%Z 
    [(0, 11); (0, 9); (0, 7); (0, 5); (0, 3); (0, 1)].
Proof.
  unfold problem_87_spec.
  unfold get_row_impl.
  simpl.
  reflexivity.
Qed.