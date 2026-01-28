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

Definition grid_ex : Grid := [[1;2;3]; [4;5;6]; [7;8;9]].

Lemma length_grid_ex : length grid_ex = 3.
Proof. reflexivity. Qed.

Lemma nth_error_grid_ex_0 : nth_error grid_ex 0 = Some [1;2;3].
Proof. reflexivity. Qed.
Lemma nth_error_grid_ex_1 : nth_error grid_ex 1 = Some [4;5;6].
Proof. reflexivity. Qed.
Lemma nth_error_grid_ex_2 : nth_error grid_ex 2 = Some [7;8;9].
Proof. reflexivity. Qed.

Lemma in_bounds_ex_00 : in_bounds_rel grid_ex (0,0).
Proof.
  eapply ibr_build with (r:=0) (c:=0); try reflexivity.
  - simpl; lia.
  - exists [1;2;3]. split; [reflexivity|simpl; lia].
Qed.

Lemma in_bounds_ex_01 : in_bounds_rel grid_ex (0,1).
Proof.
  eapply ibr_build with (r:=0) (c:=1); try reflexivity.
  - simpl; lia.
  - exists [1;2;3]. split; [reflexivity|simpl; lia].
Qed.

Lemma in_bounds_ex_10 : in_bounds_rel grid_ex (1,0).
Proof.
  eapply ibr_build with (r:=1) (c:=0); try reflexivity.
  - simpl; lia.
  - exists [4;5;6]. split; [reflexivity|simpl; lia].
Qed.

Lemma get_val_ex_00 : get_val_rel grid_ex (0,0) = 1.
Proof. reflexivity. Qed.
Lemma get_val_ex_01 : get_val_rel grid_ex (0,1) = 2.
Proof. reflexivity. Qed.
Lemma get_val_ex_10 : get_val_rel grid_ex (1,0) = 4.
Proof. reflexivity. Qed.

Lemma in_bounds_val_ge_1 :
  forall p, in_bounds_rel grid_ex p -> 1 <= get_val_rel grid_ex p.
Proof.
  intros [r c] Hin.
  inversion Hin as [grid p r0 c0 Hp Hr [row [Hrow Hc]]]; subst.
  simpl in Hr.
  destruct r0 as [|r0']; [|destruct r0' as [|r0'']]; try lia.
  - (* r=0 *)
    rewrite nth_error_grid_ex_0 in Hrow. inversion Hrow; subst row.
    assert (c0 < 3) by (simpl in Hc; assumption).
    destruct c0 as [|c0']; [simpl; lia|destruct c0' as [|c0'']; [simpl; lia|destruct c0''; [simpl; lia|lia]]].
  - (* r=1 *)
    rewrite nth_error_grid_ex_1 in Hrow. inversion Hrow; subst row.
    assert (c0 < 3) by (simpl in Hc; assumption).
    destruct c0 as [|c0']; [simpl; lia|destruct c0' as [|c0'']; [simpl; lia|destruct c0''; [simpl; lia|lia]]].
  - (* r=2 *)
    rewrite nth_error_grid_ex_2 in Hrow. inversion Hrow; subst row.
    assert (c0 < 3) by (simpl in Hc; assumption).
    destruct c0 as [|c0']; [simpl; lia|destruct c0' as [|c0'']; [simpl; lia|destruct c0''; [simpl; lia|lia]]].
Qed.

Lemma val_eq_1_pos_eq_00 :
  forall p, in_bounds_rel grid_ex p -> get_val_rel grid_ex p = 1 -> p = (0,0).
Proof.
  intros [r c] Hin Hv.
  inversion Hin as [grid p r0 c0 Hp Hr [row [Hrow Hc]]]; subst.
  simpl in Hr.
  destruct r0 as [|r0']; [|destruct r0' as [|r0'']]; try lia.
  - (* r=0 *)
    rewrite nth_error_grid_ex_0 in Hrow. inversion Hrow; subst row.
    assert (c0 < 3) by (simpl in Hc; assumption).
    destruct c0 as [|c0']; [reflexivity|destruct c0' as [|c0'']].
    + (* c=1 *)
      simpl in Hv. discriminate.
    + (* c=2 *)
      destruct c0''; [simpl in Hv; discriminate|lia].
  - (* r=1 *)
    rewrite nth_error_grid_ex_1 in Hrow. inversion Hrow; subst row.
    assert (c0 < 3) by (simpl in Hc; assumption).
    destruct c0 as [|c0']; [simpl in Hv; lia|destruct c0' as [|c0'']].
    + simpl in Hv. lia.
    + destruct c0''; [simpl in Hv; lia|lia].
  - (* r=2 *)
    rewrite nth_error_grid_ex_2 in Hrow. inversion Hrow; subst row.
    assert (c0 < 3) by (simpl in Hc; assumption).
    destruct c0 as [|c0']; [simpl in Hv; lia|destruct c0' as [|c0'']].
    + simpl in Hv. lia.
    + destruct c0''; [simpl in Hv; lia|lia].
Qed.

Lemma neighbor_00_cases :
  forall p2, neighbor_rel (0,0) p2 -> p2 = (0,1) \/ p2 = (1,0).
Proof.
  intros p2 Hn.
  inversion Hn; subst; try (left; reflexivity); try (right; reflexivity).
  - lia.
  - lia.
Qed.

Lemma path3_inv :
  forall p1 p2 p3,
    path_in_grid_rel grid_ex (p3 :: p2 :: p1 :: nil) ->
    in_bounds_rel grid_ex p1 /\
    neighbor_rel p1 p2 /\ in_bounds_rel grid_ex p2 /\
    neighbor_rel p2 p3 /\ in_bounds_rel grid_ex p3.
Proof.
  intros p1 p2 p3 H.
  inversion H; subst; try discriminate.
  (* Now Hprev: path_in_grid_rel grid_ex (p2 :: p1 :: nil), neighbor_rel p2 p3, in_bounds p3 *)
  inversion H2; subst; try discriminate.
  (* Now Hprev': path_in_grid_rel grid_ex (p1 :: nil), neighbor_rel p1 p2, in_bounds p2 *)
  inversion H5; subst.
  (* in_bounds p1 from single *)
  repeat split; assumption.
Qed.

Example find_minimum_path_testcase :
  find_minimum_path_spec grid_ex 3 [1;2;1].
Proof.
  unfold find_minimum_path_spec.
  eapply mpvr_build with (path := ( (0,0) :: (0,1) :: (0,0) :: nil)).
  - (* path_in_grid_rel *)
    eapply pigr_step.
    + eapply pigr_step.
      * eapply pigr_single. apply in_bounds_ex_00.
      * apply nr_right.
      * apply in_bounds_ex_01.
    + apply nr_left. simpl. lia.
    + apply in_bounds_ex_00.
  - (* length path = 3 *)
    simpl. reflexivity.
  - (* path_values_rel grid path [1;2;1] *)
    replace [1; 2; 1] with (map (get_val_rel grid_ex) (rev ((0,0) :: (0,1) :: (0,0) :: nil))).
    + apply pvr_def.
    + simpl. reflexivity.
  - (* minimality: forall path' of length 3, values' lex >= [1;2;1] *)
    intros path' values' Hpath' Hlen' Hvals'.
    (* shape of path' *)
    destruct path' as [|p3 [|p2 [|p1 tl]]]; simpl in Hlen'; try lia.
    destruct tl; [|simpl in Hlen'; lia].
    (* use path3_inv *)
    pose proof (path3_inv p1 p2 p3 Hpath') as [Hin1 [Hn12 [Hin2 [Hn23 Hin3]]]].
    inversion Hvals'; subst values'; clear Hvals'.
    simpl.
    set (a := get_val_rel grid_ex p1).
    set (b := get_val_rel grid_ex p2).
    set (c := get_val_rel grid_ex p3).
    assert (Ha_ge1 : 1 <= a) by (subst a; apply in_bounds_val_ge_1; exact Hin1).
    assert (Hc_ge1 : 1 <= c) by (subst c; apply in_bounds_val_ge_1; exact Hin3).
    destruct (Nat.eq_dec a 1) as [Ha1 | HaNe1].
    + (* a = 1 *)
      subst a.
      (* p1 must be (0,0) *)
      assert (p1 = (0,0)) by (apply val_eq_1_pos_eq_00; [exact Hin1 | reflexivity]).
      subst p1.
      (* p2 neighbor cases *)
      destruct (neighbor_00_cases p2 Hn12) as [Hp2_01 | Hp2_10]; subst p2; subst b.
      * (* p2 = (0,1) => b = 2 *)
        simpl.
        apply llr_eq. (* 1 = 1 *)
        apply llr_eq. (* 2 = 2 *)
        (* compare [1] <= [c] *)
        destruct c as [|c']; [simpl in Hc_ge1; lia|].
        destruct c' as [|c'']; simpl.
        -- apply llr_eq. apply llr_nil.
        -- apply llr_lt. lia.
      * (* p2 = (1,0) => b = 4 *)
        simpl.
        apply llr_eq. (* 1 = 1 *)
        apply llr_lt. lia. (* 2 < 4 *)
    + (* a <> 1, but 1 <= a => 1 < a *)
      apply llr_lt. lia.
Qed.