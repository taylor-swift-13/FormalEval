Require Import Coq.Lists.List Coq.Arith.Arith Coq.Arith.PeanoNat Coq.Arith.Compare_dec.
Import ListNotations.

Definition Grid := list (list nat).
Definition Pos := (nat * nat)%type.

Inductive in_bounds_rel : Grid -> Pos -> Prop :=
| ibr_build : forall grid p r c, p = (r, c) ->
   r < length grid ->
   (exists row, nth_error grid r = Some row /\ c < length row) ->
   in_bounds_rel grid p.

Inductive neighbor_rel : Pos -> Pos -> Prop :=
| nr_right : forall r c, neighbor_rel (r, c) (r, S c)
| nr_down : forall r c, neighbor_rel (r, c) (S r, c)
| nr_left : forall r c, 0 < c -> neighbor_rel (r, c) (r, c - 1)
| nr_up : forall r c, 0 < r -> neighbor_rel (r, c) (r - 1, c).

Definition get_val_rel (grid : Grid) (p : Pos) : nat :=
  let '(r, c) := p in
  match nth_error grid r with
  | Some row => match nth_error row c with Some v => v | None => 0 end
  | None => 0
  end.

Inductive path_in_grid_rel : Grid -> list Pos -> Prop :=
| pigr_single : forall grid p, in_bounds_rel grid p -> path_in_grid_rel grid (p :: nil)
| pigr_step : forall grid p ps q, path_in_grid_rel grid (p :: ps) ->
   neighbor_rel p q -> in_bounds_rel grid q ->
   path_in_grid_rel grid (q :: p :: ps).

Inductive path_values_rel : Grid -> list Pos -> list nat -> Prop :=
| pvr_def : forall grid path,
   path_values_rel grid path (map (get_val_rel grid) (rev path)).

Inductive lex_le_rel : list nat -> list nat -> Prop :=
| llr_nil : forall l2, lex_le_rel nil l2
| llr_lt : forall h1 t1 h2 t2, h1 < h2 -> lex_le_rel (h1 :: t1) (h2 :: t2)
| llr_eq : forall h t1 t2, lex_le_rel t1 t2 -> lex_le_rel (h :: t1) (h :: t2).

Inductive min_path_values_rel : Grid -> nat -> list nat -> Prop :=
| mpvr_build : forall grid k values path,
    path_in_grid_rel grid path -> length path = k ->
    path_values_rel grid path values ->
    (forall path' values', path_in_grid_rel grid path' -> length path' = k ->
        path_values_rel grid path' values' -> lex_le_rel values values') ->
    min_path_values_rel grid k values.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.
  
Definition find_minimum_path_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  min_path_values_rel grid k output.

Example test_find_minimum_path :
  find_minimum_path_spec [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] 3 [1; 2; 1].
Proof.
  unfold find_minimum_path_spec.
  eapply mpvr_build with (path := [(0,0);(0,1);(0,0)]).
  - apply pigr_step with (p := (0,1)) (ps := [(0,0)]) (q := (0,0)).
    + apply pigr_step with (p := (0,0)) (ps := []) (q := (0,1)).
      * apply pigr_single. apply ibr_build with (r:=0) (c:=0). reflexivity.
        simpl. lia. exists [1;2;3]. simpl. split; reflexivity.
      * apply nr_right.
      * apply ibr_build with (r:=0) (c:=1). reflexivity.
        simpl. lia. exists [1;2;3]. simpl. split; reflexivity.
    + apply nr_left. lia.
    + apply ibr_build with (r:=0) (c:=0). reflexivity.
      simpl. lia. exists [1;2;3]. simpl. split; reflexivity.
  - simpl. reflexivity.
  - apply pvr_def.
  - intros path' values' Hpath' Hlen' Hvalues'.
    destruct path' as [|(r1,c1) [(r2,c2) [(r3,c3) []]]]; simpl in Hlen'; try lia.
    inversion Hpath'; subst.
    inversion H4; subst.
    inversion H8; subst.
    inversion Hvalues'; subst.
    simpl in *.
    destruct (nth_error [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] r1) eqn:Hr1;
    destruct (nth_error l c1) eqn:Hc1; try discriminate.
    destruct (nth_error [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] r2) eqn:Hr2;
    destruct (nth_error l0 c2) eqn:Hc2; try discriminate.
    destruct (nth_error [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] r3) eqn:Hr3;
    destruct (nth_error l1 c3) eqn:Hc3; try discriminate.
    simpl in H5, H9, H13.
    assert (Hvals: map (get_val_rel [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]]) [(r3, c3); (r2, c2); (r1, c1)] = [n; n0; n1]) by assumption.
    simpl in Hvals.
    assert (Hvals': map (get_val_rel [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]]) [(0,0); (0,1); (0,0)] = [1; 2; 1]) by reflexivity.
    rewrite Hvals in Hvals'.
    destruct (lt_dec n1 1); [apply llr_lt; assumption|].
    assert (n1 = 1) by lia; subst.
    destruct (lt_dec n0 2); [apply llr_lt with (h1 := 2) (t1 := [1]) (h2 := n0) (t2 := [n])|]; try assumption.
    assert (n0 = 2) by lia; subst.
    apply llr_eq.
    destruct (lt_dec n 1); [apply llr_lt; assumption|].
    assert (n = 1) by lia; subst.
    apply llr_nil.
Qed.