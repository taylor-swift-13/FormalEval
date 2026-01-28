Require Import List.
Import ListNotations.
Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition is_valid_grid (grid : list (list Z)) (N : Z) : Prop :=
  N >= 2 /\
  Z.of_nat (length grid) = N /\
  (forall row, In row grid -> Z.of_nat (length row) = N) /\
  (forall v, 1 <= v <= N * N -> 
    exists i j, 0 <= i < N /\ 0 <= j < N /\
    nth (Z.to_nat j) (nth (Z.to_nat i) grid nil) 0 = v).

Definition get_cell (grid : list (list Z)) (i j : Z) : Z :=
  nth (Z.to_nat j) (nth (Z.to_nat i) grid nil) 0.

Definition is_neighbor (N i1 j1 i2 j2 : Z) : Prop :=
  0 <= i1 < N /\ 0 <= j1 < N /\
  0 <= i2 < N /\ 0 <= j2 < N /\
  ((i1 = i2 /\ (j2 = j1 + 1 \/ j2 = j1 - 1)) \/
   (j1 = j2 /\ (i2 = i1 + 1 \/ i2 = i1 - 1))).

Definition find_one_pos (grid : list (list Z)) (N : Z) (x y : Z) : Prop :=
  0 <= x < N /\ 0 <= y < N /\ get_cell grid x y = 1.

Definition min_neighbor_value (grid : list (list Z)) (N x y : Z) (mn : Z) : Prop :=
  (exists i j, is_neighbor N x y i j /\ get_cell grid i j = mn) /\
  (forall i j, is_neighbor N x y i j -> mn <= get_cell grid i j).

Definition minPath_spec (grid : list (list Z)) (k : Z) (result : list Z) : Prop :=
  let N := Z.of_nat (length grid) in
  is_valid_grid grid N ->
  k >= 1 ->
  exists x y mn,
    find_one_pos grid N x y /\
    min_neighbor_value grid N x y mn /\
    Z.of_nat (length result) = k /\
    (forall idx, 0 <= idx < k ->
      nth (Z.to_nat idx) result 0 = (if (idx mod 2 =? 0) then 1 else mn)).

Example test_minPath :
  minPath_spec [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] 3 [1; 2; 1].
Proof.
  unfold minPath_spec.
  intros Hvalid Hk.
  exists 0, 0, 2.
  repeat split.
  - (* find_one_pos: x bounds *)
    lia.
  - (* find_one_pos: y bounds *)
    lia.
  - (* find_one_pos: value check *)
    simpl. reflexivity.
  - (* min_neighbor_value: existence *)
    exists 0, 1.
    split.
    + unfold is_neighbor. lia.
    + simpl. reflexivity.
  - (* min_neighbor_value: minimal check *)
    intros i j Hneigh.
    unfold is_neighbor in Hneigh.
    destruct Hneigh as [Hi_bound [Hj_bound [Hi_bound2 [Hj_bound2 [ [Heq_i Hdist_j] | [Heq_j Hdist_i] ]]]]].
    + (* Same row *)
      replace i with 0 in * by lia.
      destruct Hdist_j as [Hj_plus | Hj_minus].
      * (* j = 1 *)
        replace j with 1 in * by lia.
        simpl. lia.
      * (* j = -1 *)
        lia.
    + (* Same col *)
      replace j with 0 in * by lia.
      destruct Hdist_i as [Hi_plus | Hi_minus].
      * (* i = 1 *)
        replace i with 1 in * by lia.
        simpl. lia.
      * (* i = -1 *)
        lia.
  - (* Result length check *)
    simpl. reflexivity.
  - (* Result content check *)
    intros idx Hidx.
    assert (idx = 0 \/ idx = 1 \/ idx = 2) as Hcases by lia.
    destruct Hcases as [H0 | [H1 | H2]]; subst idx; simpl; reflexivity.
Qed.