Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import Lia.

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
  | _, _ => result = []
  end.

Lemma between_4_7_is_5_or_6 : forall idx, 4 < idx < 7 -> idx = 5 \/ idx = 6.
Proof.
  intros idx [Hlt Hgt].
  destruct idx as [|i1]; try lia.
  destruct i1 as [|i2]; try lia.
  destruct i2 as [|i3]; try lia.
  destruct i3 as [|i4]; try lia.
  destruct i4 as [|i5].
  - left. reflexivity.
  - destruct i5 as [|i6].
    + right. reflexivity.
    + lia.
Qed.

Lemma idx5_saturn : forall p, get_planet_index p = Some 5 -> p = "Saturn".
Proof.
  intros p H.
  unfold get_planet_index, solar_system in H.
  simpl in H.
  destruct (String.eqb p "Mercury") eqn:HMe; simpl in H; try discriminate.
  destruct (String.eqb p "Venus") eqn:HVe; simpl in H; try discriminate.
  destruct (String.eqb p "Earth") eqn:HEa; simpl in H; try discriminate.
  destruct (String.eqb p "Mars") eqn:HMa; simpl in H; try discriminate.
  destruct (String.eqb p "Jupiter") eqn:HJu; simpl in H; try discriminate.
  destruct (String.eqb p "Saturn") eqn:HSat; simpl in H.
  - apply String.eqb_eq in HSat. exact HSat.
  - destruct (String.eqb p "Uranus") eqn:HUr; simpl in H; try discriminate.
    destruct (String.eqb p "Neptune") eqn:HNe; simpl in H; discriminate.
Qed.

Lemma idx6_uranus : forall p, get_planet_index p = Some 6 -> p = "Uranus".
Proof.
  intros p H.
  unfold get_planet_index, solar_system in H.
  simpl in H.
  destruct (String.eqb p "Mercury") eqn:HMe; simpl in H; try discriminate.
  destruct (String.eqb p "Venus") eqn:HVe; simpl in H; try discriminate.
  destruct (String.eqb p "Earth") eqn:HEa; simpl in H; try discriminate.
  destruct (String.eqb p "Mars") eqn:HMa; simpl in H; try discriminate.
  destruct (String.eqb p "Jupiter") eqn:HJu; simpl in H; try discriminate.
  destruct (String.eqb p "Saturn") eqn:HSat; simpl in H; try discriminate.
  destruct (String.eqb p "Uranus") eqn:HUr; simpl in H.
  - apply String.eqb_eq in HUr. exact HUr.
  - destruct (String.eqb p "Neptune") eqn:HNe; simpl in H; discriminate.
Qed.

Example test_bf_Jupiter_Neptune :
  problem_148_spec "Jupiter" "Neptune" ["Saturn"; "Uranus"].
Proof.
  unfold problem_148_spec.
  assert (HJup : get_planet_index "Jupiter" = Some 4) by (vm_compute; reflexivity).
  assert (HNept : get_planet_index "Neptune" = Some 7) by (vm_compute; reflexivity).
  rewrite HJup, HNept. simpl.
  split.
  - intros p. split; intros HIn.
    + simpl in HIn. destruct HIn as [HS | [HU | []]]; subst.
      * exists 5. split; [vm_compute; reflexivity|lia].
      * exists 6. split; [vm_compute; reflexivity|lia].
    + destruct HIn as [idx [Hidx Hrange]].
      pose proof (between_4_7_is_5_or_6 idx Hrange) as Hcases.
      destruct Hcases as [H5 | H6]; subst.
      * apply idx5_saturn in Hidx. subst. simpl. left. reflexivity.
      * apply idx6_uranus in Hidx. subst. simpl. right. left. reflexivity.
  - intros p_a p_b i j Hi Hj Hij.
    destruct i as [|i'].
    + simpl in Hi.
      destruct j as [|j'].
      * lia.
      * destruct j' as [|j''].
        -- simpl in Hj. inversion Hi; subst p_a.
           inversion Hj; subst p_b.
           exists 5, 6.
           split; [vm_compute; reflexivity|].
           split; [vm_compute; reflexivity|lia].
        -- simpl in Hj. discriminate Hj.
    + destruct i' as [|i''].
      * simpl in Hi.
        destruct j as [|j'].
        -- lia.
        -- destruct j' as [|j''].
           ++ simpl in Hj. lia.
           ++ simpl in Hj. discriminate Hj.
      * simpl in Hi. discriminate Hi.
Qed.