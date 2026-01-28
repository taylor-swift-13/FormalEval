Require Import Coq.Lists.List Coq.Arith.Arith.
Require Import Lia.
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

Definition test_grid : Grid := [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]].

Lemma in_bounds_0_0 : in_bounds_rel test_grid (0, 0).
Proof.
  eapply ibr_build; [reflexivity | simpl; lia | ].
  exists [1; 2; 3]. simpl. split; [reflexivity | lia].
Qed.

Lemma in_bounds_0_1 : in_bounds_rel test_grid (0, 1).
Proof.
  eapply ibr_build; [reflexivity | simpl; lia | ].
  exists [1; 2; 3]. simpl. split; [reflexivity | lia].
Qed.

Lemma path_valid : path_in_grid_rel test_grid [(0, 0); (0, 1); (0, 0)].
Proof.
  apply pigr_step with (p := (0, 1)) (ps := [(0, 0)]).
  - apply pigr_step with (p := (0, 0)) (ps := []).
    + apply pigr_single. apply in_bounds_0_0.
    + apply nr_right.
    + apply in_bounds_0_1.
  - assert (H: (0, 0) = (0, 1 - 1)) by (simpl; reflexivity).
    rewrite H. apply nr_left. lia.
  - apply in_bounds_0_0.
Qed.

Lemma path_values_121 : path_values_rel test_grid [(0, 0); (0, 1); (0, 0)] [1; 2; 1].
Proof.
  assert (H: [1; 2; 1] = map (get_val_rel test_grid) (rev [(0, 0); (0, 1); (0, 0)])).
  { simpl. reflexivity. }
  rewrite H. apply pvr_def.
Qed.

Lemma get_val_bounds : forall r c,
  r < 3 -> c < 3 ->
  get_val_rel test_grid (r, c) >= 1.
Proof.
  intros r c Hr Hc.
  unfold get_val_rel, test_grid.
  destruct r as [|[|[|r']]]; try lia;
  destruct c as [|[|[|c']]]; try lia; simpl; lia.
Qed.

Lemma get_val_eq_1 : forall r c,
  r < 3 -> c < 3 ->
  get_val_rel test_grid (r, c) = 1 -> (r = 0 /\ c = 0).
Proof.
  intros r c Hr Hc Hval.
  unfold get_val_rel, test_grid in Hval.
  destruct r as [|[|[|r']]]; try lia;
  destruct c as [|[|[|c']]]; try lia; simpl in Hval; try lia.
  auto.
Qed.

Lemma neighbor_0_0_vals : forall p,
  neighbor_rel (0, 0) p ->
  in_bounds_rel test_grid p ->
  get_val_rel test_grid p >= 2.
Proof.
  intros p Hn Hib.
  inversion Hn; subst.
  - simpl. lia.
  - simpl. lia.
  - lia.
  - lia.
Qed.

Lemma lex_le_refl : forall l, lex_le_rel l l.
Proof.
  induction l; constructor; auto.
Qed.

Example test_find_minimum_path :
  find_minimum_path_spec test_grid 3 [1; 2; 1].
Proof.
  unfold find_minimum_path_spec.
  eapply mpvr_build with (path := [(0, 0); (0, 1); (0, 0)]).
  - apply path_valid.
  - reflexivity.
  - apply path_values_121.
  - intros path' values' Hpath' Hlen' Hvals'.
    inversion Hvals' as [g pth Heq]. subst values'.
    destruct path' as [|p1 rest1]; [simpl in Hlen'; discriminate|].
    destruct rest1 as [|p2 rest2]; [simpl in Hlen'; discriminate|].
    destruct rest2 as [|p3 rest3]; [simpl in Hlen'; discriminate|].
    destruct rest3 as [|p4 rest4]; [|simpl in Hlen'; discriminate].
    simpl.
    inversion Hpath' as [|g' pp ps qq Hprev Hneigh Hib Heq1 Heq2]. subst.
    inversion Hprev as [|g'' pp' ps' qq' Hprev' Hneigh' Hib' Heq3 Heq4]. subst.
    inversion Hprev' as [g''' p''' Hib'' Heq5 | ]. subst.
    inversion Hib'' as [g4 pos r3 c3 Heqp Hr3 Hex3]. subst.
    destruct Hex3 as [row3 [Hrow3 Hc3]].
    unfold test_grid in Hr3, Hrow3, Hc3. simpl in Hr3.
    assert (Hr3' : r3 < 3) by lia.
    destruct r3 as [|[|[|r3']]]; try lia.
    + simpl in Hrow3. inversion Hrow3. subst. simpl in Hc3.
      destruct c3 as [|[|[|c3']]]; try lia.
      * simpl.
        inversion Hneigh'; subst.
        -- simpl. apply llr_eq.
           inversion Hneigh; subst.
           ++ simpl. apply llr_eq. apply llr_lt. lia.
           ++ simpl. apply llr_eq. apply llr_lt. lia.
           ++ simpl. apply llr_eq. apply llr_eq. apply llr_nil.
           ++ lia.
        -- simpl. apply llr_eq. apply llr_lt. lia.
        -- lia.
        -- lia.
      * simpl. apply llr_lt. lia.
      * simpl. apply llr_lt. lia.
    + simpl in Hrow3. inversion Hrow3. subst. simpl in Hc3.
      destruct c3 as [|[|[|c3']]]; try lia; simpl; apply llr_lt; lia.
    + simpl in Hrow3. inversion Hrow3. subst. simpl in Hc3.
      destruct c3 as [|[|[|c3']]]; try lia; simpl; apply llr_lt; lia.
Qed.