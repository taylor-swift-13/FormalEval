Require Import Coq.Lists.List Coq.Arith.Arith Coq.Arith.PeanoNat Coq.micromega.Lia.
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

(* Test input and output *)
Definition test_grid : Grid :=
  [[1;2;3]; [4;5;6]; [7;8;9]].

Definition test_k := 3.
Definition test_output := [1;2;1].

(* Auxiliary lemmas *)

Lemma in_bounds_rel_intro :
  forall grid r c,
    r < length grid ->
    (exists row, nth_error grid r = Some row /\ c < length row) ->
    in_bounds_rel grid (r, c).
Proof.
  intros. eapply ibr_build; eauto.
Qed.

Lemma nr_0_0_0_1 : neighbor_rel (0,0) (0,1).
Proof. constructor. Qed.

Lemma nr_0_1_1_1 : neighbor_rel (0,1) (1,1).
Proof. constructor. Qed.

Lemma nr_1_1_0_1 : neighbor_rel (1,1) (0,1).
Proof. constructor 4. lia. Qed.

Lemma in_bounds_0_0 : in_bounds_rel test_grid (0,0).
Proof.
  apply in_bounds_rel_intro with (r:=0) (c:=0).
  - simpl; lia.
  - exists [1;2;3]. simpl; split; lia.
Qed.

Lemma in_bounds_0_1 : in_bounds_rel test_grid (0,1).
Proof.
  apply in_bounds_rel_intro with (r:=0) (c:=1).
  - simpl; lia.
  - exists [1;2;3]. simpl; split; lia.
Qed.

Lemma in_bounds_1_1 : in_bounds_rel test_grid (1,1).
Proof.
  apply in_bounds_rel_intro with (r:=1) (c:=1).
  - simpl; lia.
  - exists [4;5;6]. simpl; split; lia.
Qed.

(* Define the minimal path: (1,1)->(0,1)->(0,0) reversed *)
Definition test_path : list Pos := [(1,1); (0,1); (0,0)].

Lemma path_in_grid_test_path :
  path_in_grid_rel test_grid test_path.
Proof.
  apply pigr_step with (p := (0,1)) (ps := [(0,0)]) (q := (1,1)).
  - apply pigr_step with (p := (0,0)) (ps := []) (q := (0,1)).
    + apply pigr_single; apply in_bounds_0_0.
    + apply nr_0_0_0_1.
    + apply in_bounds_0_1.
  - apply nr_0_1_1_1.
  - apply in_bounds_1_1.
Qed.

Lemma path_values_test_path :
  path_values_rel test_grid test_path test_output.
Proof.
  simpl; constructor.
Qed.

(* get_val_rel always ≥ 1 on test_grid *)
Lemma get_val_rel_ge_1 :
  forall p,
    in_bounds_rel test_grid p ->
    1 <= get_val_rel test_grid p.
Proof.
  intros (r,c) H.
  inversion H; subst.
  unfold get_val_rel.
  destruct (nth_error test_grid r) eqn:Hr.
  - destruct (nth_error l c) eqn:Hc.
    + lia.
    + destruct H2 as [_ [_ Hcl]].
      rewrite Hr in H1. inversion H1.
      lia.
  - destruct H2 as [_ [Hneq _]].
    rewrite Hr in Hneq. discriminate.
Qed.

(* lex_le_rel is reflexive *)
Lemma lex_le_refl : forall l, lex_le_rel l l.
Proof.
  induction l.
  - constructor.
  - constructor 3. assumption.
Qed.

(* Main minimality lemma *)
Lemma test_minimality :
  forall path' values',
    path_in_grid_rel test_grid path' ->
    length path' = 3 ->
    path_values_rel test_grid path' values' ->
    lex_le_rel test_output values'.
Proof.
  intros path' values' Hin Hlen Hpvals.
  inversion Hpvals; subst; clear Hpvals.
  destruct path' as [|p1 path''].
  - simpl in Hlen; lia.
  destruct path'' as [|p2 path'''].
  + simpl in Hlen; lia.
  destruct path''' as [|p3 path''''].
  * simpl in Hlen; lia.
  * simpl in Hlen; subst.
    set (v1 := get_val_rel test_grid p3).
    set (v2 := get_val_rel test_grid p2).
    set (v3 := get_val_rel test_grid p1).
    assert (H1 : 1 <= v3).
    { apply get_val_rel_ge_1.
      revert Hin.
      generalize (p3 :: []).
      induction path'; intros Hin'.
      - inversion Hin'.
      - inversion Hin'; subst; eauto.
    }
    destruct (Nat.lt_ge_cases 1 v3) as [Hlt | Hge].
    - constructor 2; assumption.
    - assert (v3 = 1) by lia; subst v3.
      assert (H2 : 2 <= v2).
      { apply get_val_rel_ge_1.
        revert Hin.
        generalize (p2 :: p3 :: []).
        induction path'; intros Hin'.
        - inversion Hin'.
        - inversion Hin'; subst; eauto.
      }
      destruct (Nat.lt_ge_cases 2 v2) as [Hlt2|Hge2].
      + constructor 3. constructor 2; assumption.
      + assert (v2 = 2) by lia; subst v2.
        assert (H3 : 1 <= v1).
        { apply get_val_rel_ge_1.
          revert Hin.
          generalize (p1 :: p2 :: p3 :: []).
          induction path'; intros Hin'.
          - inversion Hin'.
          - inversion Hin'; subst; eauto.
        }
        destruct (Nat.lt_ge_cases 1 v1) as [Hlt3|Hge3].
        * constructor 3. constructor 3. constructor 2; assumption.
        * constructor 3. constructor 3. constructor 3.
          apply lex_le_refl.
Qed.

Example test_case :
  find_minimum_path_spec test_grid test_k test_output.
Proof.
  unfold find_minimum_path_spec.
  eapply mpvr_build with (path := test_path).
  - apply path_in_grid_test_path.
  - reflexivity.
  - apply path_values_test_path.
  - apply test_minimality.
Qed.