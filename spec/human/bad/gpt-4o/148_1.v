(* 引入必要的 Coq 库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.

Import ListNotations.
Local Open Scope string_scope.

Definition solar_system : list string :=
  [ "Mercury"; "Venus"; "Earth"; "Mars"; "Jupiter"; "Saturn"; "Uranus"; "Neptune" ].

Definition get_planet_index (p_name : string) : option nat :=
  snd (
    fold_left (fun acc p =>
      let '(i, res) := acc in
      match res with
      | Some _ => (S i, res)
      | None => if String.eqb p p_name then (S i, Some i) else (S i, None)
      end) solar_system (0, None)).

Definition bf (planet1 planet2 : string) : list string :=
  match (get_planet_index planet1), (get_planet_index planet2) with
  | Some idx1, Some idx2 =>
    let min_idx := min idx1 idx2 in
    let max_idx := max idx1 idx2 in
    filter (fun p =>
      match get_planet_index p with
      | Some idx => andb (min_idx <? idx) (idx <? max_idx)
      | None => false
      end) solar_system
  | _, _ => []
  end.

Definition problem_148_pre (planet1 planet2 : string) : Prop := True.

Definition problem_148_spec (planet1 planet2 : string) (result : list string) : Prop :=
  match (get_planet_index planet1), (get_planet_index planet2) with
  | Some idx1, Some idx2 =>
    let min_idx := min idx1 idx2 in
    let max_idx := max idx1 idx2 in
    (forall p, In p result <->
      (exists idx, get_planet_index p = Some idx /\
                   min_idx < idx < max_idx))
    /\
    (forall p_a p_b i j,
      nth_error result i = Some p_a ->
      nth_error result j = Some p_b ->
      i < j ->
      (exists idx_a idx_b,
         get_planet_index p_a = Some idx_a /\
         get_planet_index p_b = Some idx_b /\
         idx_a < idx_b))

  | _, _ => result = []
  end.

(* 引入辅助引理：如果行星在 solar_system 中，则可以获取其索引 *)
Lemma In_get_planet_index : forall p,
  In p solar_system ->
  exists idx, get_planet_index p = Some idx.
Proof.
  intros p H.
  unfold get_planet_index.
  induction solar_system as [| h t IH].
  - simpl in H. contradiction.
  - simpl in H. destruct H as [H | H].
    + subst. simpl. exists 0. rewrite String.eqb_refl. reflexivity.
    + simpl. destruct (fold_left (fun acc p0 =>
        let '(i, res) := acc in
        match res with
        | Some _ => (S i, res)
        | None => if String.eqb p0 p then (S i, Some i) else (S i, None)
        end) t (0, None)) eqn:Hfold.
      destruct o as [idx | ] eqn:Hidx.
      * exists (S n). fold (get_planet_index p).
        rewrite Hfold. simpl. destruct (String.eqb h p) eqn:Heqb.
        -- apply String.eqb_eq in Heqb. subst. contradiction.
        -- reflexivity.
      * apply IH in H as [idx Hidx].
        exists (S idx). fold (get_planet_index p).
        rewrite Hfold. simpl. destruct (String.eqb h p) eqn:Heqb.
        -- apply String.eqb_eq in Heqb. subst. contradiction.
        -- assumption.
Qed.

Theorem bf_correct : forall planet1 planet2,
  problem_148_pre planet1 planet2 ->
  problem_148_spec planet1 planet2 (bf planet1 planet2).
Proof.
  intros planet1 planet2 _.
  unfold bf, problem_148_spec.
  destruct (get_planet_index planet1) eqn: H1; destruct (get_planet_index planet2) eqn: H2.
  - (* Both planets are valid *)
    simpl. split.
    + intros p. split.
      * intros In_p. apply filter_In in In_p. destruct In_p as [In_p Cond].
        apply In_get_planet_index in In_p as [idx Hidx].
        simpl in Cond. rewrite Hidx in Cond.
        apply andb_true_iff in Cond. destruct Cond as [Hmin Hmax].
        apply Nat.ltb_lt in Hmin. apply Nat.ltb_lt in Hmax.
        exists idx. split; assumption.
      * intros [idx [Hidx Hrange]]. apply filter_In.
        split.
        -- apply In_get_planet_index. exists idx. assumption.
        -- simpl. rewrite Hidx. apply andb_true_iff. split.
           ++ apply Nat.ltb_lt. apply Hrange.
           ++ apply Nat.ltb_lt. apply Hrange.
    + intros p_a p_b i j Ha Hb Hij.
      apply nth_error_In in Ha. apply nth_error_In in Hb.
      apply filter_In in Ha as [Ha Cond_a]. apply filter_In in Hb as [Hb Cond_b].
      apply In_get_planet_index in Ha as [idx_a Ha_idx].
      apply In_get_planet_index in Hb as [idx_b Hb_idx].
      exists idx_a, idx_b. split; [assumption | split; [assumption | lia]].
  - (* Invalid planet names *)
    reflexivity.
  - (* Invalid planet names *)
    reflexivity.
  - (* Invalid planet names *)
    reflexivity.
Qed.

Example test_bf_Jupiter_Neptune :
  bf "Jupiter" "Neptune" = ["Saturn"; "Uranus"].
Proof.
  simpl. reflexivity.
Qed.