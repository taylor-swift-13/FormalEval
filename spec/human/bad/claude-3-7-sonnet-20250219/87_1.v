Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
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

(* Proof of the test case *)

Example get_row_example :
  problem_87_spec
    [[1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z];
     [1%Z; 2%Z; 3%Z; 4%Z; 1%Z; 6%Z];
     [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 1%Z]]
    1%Z
    [(0, 0); (1, 4); (1, 0); (2, 5); (2, 0)].
Proof.
  unfold problem_87_spec, get_row_impl.

  (* Simplify collect_coords_row for each row *)

  assert (Hrow0 : collect_coords_row [1;2;3;4;5;6] 0 0 1 = [(0,0)]).
  {
    simpl.
    rewrite Z.eqb_refl.
    simpl.
    repeat (rewrite Z.eqb_neq; try lia).
    simpl.
    reflexivity.
  }

  assert (Hrow1 : collect_coords_row [1;2;3;4;1;6] 1 0 1 = [(1,0); (1,4)]).
  {
    simpl.
    rewrite Z.eqb_refl.
    simpl.
    repeat (rewrite Z.eqb_neq; try lia).
    simpl.
    rewrite Z.eqb_refl.
    simpl.
    repeat (rewrite Z.eqb_neq; try lia).
    simpl.
    reflexivity.
  }

  assert (Hrow2 : collect_coords_row [1;2;3;4;5;1] 2 0 1 = [(2,0); (2,5)]).
  {
    simpl.
    rewrite Z.eqb_refl.
    simpl.
    repeat (rewrite Z.eqb_neq; try lia).
    simpl.
    rewrite Z.eqb_refl.
    simpl.
    reflexivity.
  }

  (* Simplify collect_all_coords *)
  unfold collect_all_coords.
  simpl.
  rewrite Hrow0, Hrow1, Hrow2.
  clear Hrow0 Hrow1 Hrow2.

  (* So the unsorted list is [(0,0); (1,0); (1,4); (2,0); (2,5)] *)

  (* Now show sorting produces [(0,0); (1,4); (1,0); (2,5); (2,0)] *)

  (* Evaluate sort_coords *)
  unfold sort_coords; simpl.

  (* sort_coords [(0,0); (1,0); (1,4); (2,0); (2,5)] = insert_coord (0,0) (sort_coords [(1,0); (1,4); (2,0); (2,5)]) *)

  remember (sort_coords [(1,0); (1,4); (2,0); (2,5)]) as s1.

  (* sort_coords [(1,0); (1,4); (2,0); (2,5)] = insert_coord (1,0) (sort_coords [(1,4); (2,0); (2,5)]) *)

  remember (sort_coords [(1,4); (2,0); (2,5)]) as s2.

  (* sort_coords [(1,4); (2,0); (2,5)] = insert_coord (1,4) (sort_coords [(2,0); (2,5)]) *)

  remember (sort_coords [(2,0); (2,5)]) as s3.

  (* sort_coords [(2,0); (2,5)] = insert_coord (2,0) (sort_coords [(2,5)]) *)

  remember (sort_coords [(2,5)]) as s4.

  simpl in s4.
  (* sort_coords [(2,5)] = insert_coord (2,5) [] = [(2,5)] *)
  inversion s4; subst; clear s4.

  simpl in s3.
  (* insert_coord (2,0) [(2,5)] *)
  unfold insert_coord.
  simpl.

  (* Compare fst: 2 vs 2 (eq) *)
  destruct (Z.eqb 2 2) eqn:Heq.
  - (* Compare columns: is 5 < 0? *)
    destruct (Z.ltb 5 0) eqn:Hlt.
    + lia. (* false *)
    + (* false: insert (2,0) after (2,5) *)
      simpl in s3.
      inversion s3; subst; clear s3.
  - lia. (* false *)
  (* So s3 = [(2,5); (2,0)] *)

  simpl in s2.
  (* insert_coord (1,4) [(2,5); (2,0)] *)
  unfold insert_coord.
  simpl.
  destruct (Z.ltb 1 2) eqn:Hlt.
  - simpl in s2.
    inversion s2; subst; clear s2.
  - lia. (* false *)
  (* s2 = (1,4) :: [(2,5); (2,0)] *)

  simpl in s1.
  (* insert_coord (1,0) s2 = insert_coord (1,0) [(1,4); (2,5); (2,0)] *)
  unfold insert_coord.
  simpl.
  destruct (Z.ltb 1 1) eqn:Hlt_eq.
  - lia. (* false *)
  - destruct (Z.eqb 1 1) eqn:Heq_eq.
    + destruct (Z.ltb 4 0) eqn:Hcol.
      * lia. (* false *)
      * simpl.
        (* insert_coord (1,0) [(2,5); (2,0)] *)
        unfold insert_coord.
        simpl.
        destruct (Z.ltb 1 2) eqn:Hlt2.
        -- simpl.
           inversion s1; subst; clear s1.
        -- lia. (* false *)
    + lia. (* false *)

  (* s1 = [(1,4); (1,0); (2,5); (2,0)] *)

  (* Finally insert_coord (0,0) s1 *)
  unfold insert_coord.
  simpl.
  destruct (Z.ltb 0 1) eqn:Hlt0.
  - simpl.
    reflexivity.
  - lia. (* false *)
Qed.