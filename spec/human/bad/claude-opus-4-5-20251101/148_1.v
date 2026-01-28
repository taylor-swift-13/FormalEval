Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

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
  | _, _ =>
    result = []
  end.

(* Helper lemmas for computing planet indices *)
Lemma get_planet_index_Jupiter : get_planet_index "Jupiter" = Some 4.
Proof. reflexivity. Qed.

Lemma get_planet_index_Neptune : get_planet_index "Neptune" = Some 7.
Proof. reflexivity. Qed.

Lemma get_planet_index_Saturn : get_planet_index "Saturn" = Some 5.
Proof. reflexivity. Qed.

Lemma get_planet_index_Uranus : get_planet_index "Uranus" = Some 6.
Proof. reflexivity. Qed.

Lemma get_planet_index_Mercury : get_planet_index "Mercury" = Some 0.
Proof. reflexivity. Qed.

Lemma get_planet_index_Venus : get_planet_index "Venus" = Some 1.
Proof. reflexivity. Qed.

Lemma get_planet_index_Earth : get_planet_index "Earth" = Some 2.
Proof. reflexivity. Qed.

Lemma get_planet_index_Mars : get_planet_index "Mars" = Some 3.
Proof. reflexivity. Qed.

(* Helper: index uniquely determines planet for indices 5 and 6 *)
Lemma planet_index_5_is_Saturn : forall p,
  get_planet_index p = Some 5 -> p = "Saturn".
Proof.
  intros p H.
  unfold get_planet_index in H.
  simpl in H.
  destruct (String.eqb "Mercury" p) eqn:E1; simpl in H; try discriminate.
  destruct (String.eqb "Venus" p) eqn:E2; simpl in H; try discriminate.
  destruct (String.eqb "Earth" p) eqn:E3; simpl in H; try discriminate.
  destruct (String.eqb "Mars" p) eqn:E4; simpl in H; try discriminate.
  destruct (String.eqb "Jupiter" p) eqn:E5; simpl in H; try discriminate.
  destruct (String.eqb "Saturn" p) eqn:E6; simpl in H.
  - apply String.eqb_eq in E6. symmetry. exact E6.
  - destruct (String.eqb "Uranus" p) eqn:E7; simpl in H; try discriminate.
    destruct (String.eqb "Neptune" p) eqn:E8; simpl in H; discriminate.
Qed.

Lemma planet_index_6_is_Uranus : forall p,
  get_planet_index p = Some 6 -> p = "Uranus".
Proof.
  intros p H.
  unfold get_planet_index in H.
  simpl in H.
  destruct (String.eqb "Mercury" p) eqn:E1; simpl in H; try discriminate.
  destruct (String.eqb "Venus" p) eqn:E2; simpl in H; try discriminate.
  destruct (String.eqb "Earth" p) eqn:E3; simpl in H; try discriminate.
  destruct (String.eqb "Mars" p) eqn:E4; simpl in H; try discriminate.
  destruct (String.eqb "Jupiter" p) eqn:E5; simpl in H; try discriminate.
  destruct (String.eqb "Saturn" p) eqn:E6; simpl in H; try discriminate.
  destruct (String.eqb "Uranus" p) eqn:E7; simpl in H.
  - apply String.eqb_eq in E7. symmetry. exact E7.
  - destruct (String.eqb "Neptune" p) eqn:E8; simpl in H; discriminate.
Qed.

Example problem_148_test1 :
  problem_148_spec "Jupiter" "Neptune" ["Saturn"; "Uranus"].
Proof.
  unfold problem_148_spec.
  rewrite get_planet_index_Jupiter.
  rewrite get_planet_index_Neptune.
  simpl.
  split.
  - (* Property 1 *)
    intro p.
    split.
    + (* -> direction *)
      intro HIn.
      simpl in HIn.
      destruct HIn as [Heq | [Heq | Hcontra]].
      * subst p. exists 5. split. reflexivity. split; auto.
      * subst p. exists 6. split. reflexivity. split; auto.
      * destruct Hcontra.
    + (* <- direction *)
      intros [idx [Hidx [Hlt Hgt]]].
      assert (idx = 5 \/ idx = 6) as Hcases.
      { destruct idx. inversion Hlt.
        destruct idx. inversion Hlt. inversion H0.
        destruct idx. inversion Hlt. inversion H0. inversion H1.
        destruct idx. inversion Hlt. inversion H0. inversion H1. inversion H2.
        destruct idx. inversion Hlt. inversion H0. inversion H1. inversion H2. inversion H3.
        destruct idx. left. reflexivity.
        destruct idx. right. reflexivity.
        destruct idx. inversion Hgt. inversion Hgt. }
      destruct Hcases as [Hidx5 | Hidx6].
      * subst idx. apply planet_index_5_is_Saturn in Hidx. subst p. simpl. left. reflexivity.
      * subst idx. apply planet_index_6_is_Uranus in Hidx. subst p. simpl. right. left. reflexivity.
  - (* Property 2 *)
    intros p_a p_b i j Hi Hj Hij.
    destruct i as [|i'].
    + simpl in Hi. inversion Hi. subst p_a. clear Hi.
      destruct j as [|j']. inversion Hij.
      destruct j' as [|j''].
      * simpl in Hj. inversion Hj. subst p_b. clear Hj.
        exists 5, 6. split. reflexivity. split. reflexivity. auto.
      * simpl in Hj. destruct j''; discriminate.
    + destruct i' as [|i''].
      * simpl in Hi. inversion Hi. subst p_a. clear Hi.
        destruct j as [|j']. inversion Hij.
        destruct j' as [|j'']. inversion Hij. inversion H0.
        simpl in Hj. destruct j''; discriminate.
      * simpl in Hi. destruct i''; discriminate.
Qed.