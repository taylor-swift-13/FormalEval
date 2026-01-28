Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Local Open Scope string_scope.

(* Solar system definition *)
Definition solar_system : list string :=
  ["Mercury"; "Venus"; "Earth"; "Mars"; "Jupiter"; "Saturn"; "Uranus"; "Neptune"].

(* Get planet index using fold_left *)
Definition get_planet_index (p_name : string) : option nat :=
  snd (fold_left 
    (fun '(i, res) p => 
      match res with
      | Some _ => (S i, res)
      | None => if String.eqb p p_name then (S i, Some i) else (S i, None)
      end)
    solar_system (0, None)).

(* Custom min and max functions since Coq.Arith.MinMax might not be available *)
Definition min (a b : nat) : nat := if a <=? b then a else b.
Definition max (a b : nat) : nat := if a <=? b then b else a.

(* Specification *)
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

(* Helper lemma: get_planet_index correctness *)
Lemma planet_indices_correct : 
  (get_planet_index "Mercury" = Some 0) /\
  (get_planet_index "Venus" = Some 1) /\
  (get_planet_index "Earth" = Some 2) /\
  (get_planet_index "Mars" = Some 3) /\
  (get_planet_index "Jupiter" = Some 4) /\
  (get_planet_index "Saturn" = Some 5) /\
  (get_planet_index "Uranus" = Some 6) /\
  (get_planet_index "Neptune" = Some 7).
Proof.
  repeat split; unfold get_planet_index, solar_system;
  simpl; reflexivity.
Qed.

(* Helper lemmas for min/max *)
Lemma min_4_7 : min 4 7 = 4.
Proof. unfold min. simpl. reflexivity. Qed.

Lemma max_4_7 : max 4 7 = 7.
Proof. unfold max. simpl. reflexivity. Qed.

(* Test case proof *)
Example test_jupiter_neptune : 
  problem_148_spec "Jupiter" "Neptune" ["Saturn"; "Uranus"].
Proof.
  unfold problem_148_spec.
  destruct planet_indices_correct as [Hmercury [Hvenus [Hearth [Hmars [Hjupiter [Hsaturn [Huranus Hneptune]]]]]]].
  rewrite Hjupiter, Hneptune.
  rewrite min_4_7, max_4_7.
  split.
  - (* First property: membership condition *)
    intros p. split.
    + intros H. simpl in H. destruct H as [H | H].
      * rewrite H. exists 5. split.
        { exact Hsaturn. }
        { simpl. lia. }
      * destruct H as [H | H].
        { rewrite H. exists 6. split.
          { exact Huranus. }
          { simpl. lia. }
        }
        { contradiction. }
    + intros H. destruct H as [idx [Hidx Hrange]].
      destruct (String.eqb_spec p "Saturn").
      * left. symmetry. assumption.
      * destruct (String.eqb_spec p "Uranus").
        { right. left. symmetry. assumption. }
        { destruct Hidx.
          - rewrite Hmercury in H. inversion H.
          - rewrite Hvenus in H. inversion H.
          - rewrite Hearth in H. inversion H.
          - rewrite Hmars in H. inversion H.
          - rewrite Hjupiter in H. inversion H.
          - rewrite Hsaturn in H. inversion H. subst. contradiction.
          - rewrite Huranus in H. inversion H. subst. contradiction.
          - rewrite Hneptune in H. inversion H.
        }
  - (* Second property: sorted order *)
    intros p_a p_b i j H1 H2 Hlt.
    destruct i as [|i]; destruct j as [|j]; try lia.
    + (* i = 0, j = 1 *)
      simpl in H1, H2.
      inversion H1. inversion H2. subst p_a p_b.
      exists 5, 6. repeat split.
      * exact Hsaturn.
      * exact Huranus.
      * lia.
    + (* Other cases lead to contradiction *)
      destruct i as [|i]; destruct j as [|j]; try lia;
      simpl in H1, H2; discriminate.
Qed.