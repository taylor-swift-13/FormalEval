Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.

Import ListNotations.
Local Open Scope string_scope.

(* Definition of Solar System *)
Definition solar_system : list string :=
  [ "Mercury"; "Venus"; "Earth"; "Mars"; "Jupiter"; "Saturn"; "Uranus"; "Neptune" ].

(* Helper function to get planet index *)
Definition get_planet_index (p_name : string) : option nat :=
  snd (
    fold_left (fun acc p =>
      let '(i, res) := acc in
      match res with
      | Some _ => (S i, res)
      | None => if String.eqb p p_name then (S i, Some i) else (S i, None)
      end) solar_system (0, None)).

(* Precondition *)
Definition problem_148_pre (planet1 planet2 : string) : Prop := True.

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

  | _, _ =>
    result = []
  end.

(* Proof for the test case *)
Example test_bf_jupiter_neptune :
  problem_148_spec "Jupiter" "Neptune" ["Saturn"; "Uranus"].
Proof.
  unfold problem_148_spec.
  (* Simplification evaluates get_planet_index for "Jupiter" (4) and "Neptune" (7) *)
  (* min_idx = 4, max_idx = 7 *)
  simpl.
  split.
  
  (* Part 1: Membership Property *)
  - intros p. split.
    + (* Direction: In result -> Condition *)
      intros H_in.
      destruct H_in as [H_sat | [H_ura | H_end]].
      * (* Case: p = "Saturn" *)
        subst p. exists 5. split.
        -- reflexivity. (* get_planet_index "Saturn" = Some 5 *)
        -- lia.         (* 4 < 5 < 7 *)
      * (* Case: p = "Uranus" *)
        subst p. exists 6. split.
        -- reflexivity. (* get_planet_index "Uranus" = Some 6 *)
        -- lia.         (* 4 < 6 < 7 *)
      * (* Case: End of list *)
        contradiction.
    
    + (* Direction: Condition -> In result *)
      intros [idx [H_idx H_range]].
      (* H_idx: get_planet_index p = Some idx *)
      (* H_range: 4 < idx < 7 *)
      
      unfold get_planet_index in H_idx.
      simpl in H_idx.
      
      (* The term H_idx contains nested matches on (String.eqb "PlanetName" p).
         We must destruct these terms in the order they appear (Mercury to Neptune)
         to simplify H_idx. Note the order of arguments in String.eqb. *)
      destruct (String.eqb "Mercury" p) eqn:E1; [inversion H_idx; subst; lia | ].
      destruct (String.eqb "Venus" p) eqn:E2; [inversion H_idx; subst; lia | ].
      destruct (String.eqb "Earth" p) eqn:E3; [inversion H_idx; subst; lia | ].
      destruct (String.eqb "Mars" p) eqn:E4; [inversion H_idx; subst; lia | ].
      destruct (String.eqb "Jupiter" p) eqn:E5; [inversion H_idx; subst; lia | ].
      destruct (String.eqb "Saturn" p) eqn:E6.
      * (* Case: p = "Saturn" *)
        apply String.eqb_eq in E6. subst p.
        left. reflexivity.
      * destruct (String.eqb "Uranus" p) eqn:E7.
        -- (* Case: p = "Uranus" *)
           apply String.eqb_eq in E7. subst p.
           right. left. reflexivity.
        -- destruct (String.eqb "Neptune" p) eqn:E8; [inversion H_idx; subst; lia | ].
           (* Case: p is none of the planets *)
           inversion H_idx.

  (* Part 2: Sortedness Property *)
  - intros p_a p_b i j H_nth_a H_nth_b H_lt.
    (* The result list is ["Saturn"; "Uranus"] with length 2. Indices are 0 and 1. *)
    destruct i.
    + (* i = 0, p_a should be "Saturn" *)
      simpl in H_nth_a. injection H_nth_a as H_pa. subst p_a.
      destruct j.
      * (* j = 0 *) lia. (* i < j -> 0 < 0 -> False *)
      * destruct j.
        -- (* j = 1, p_b should be "Uranus" *)
           simpl in H_nth_b. injection H_nth_b as H_pb. subst p_b.
           exists 5. exists 6.
           split. { reflexivity. } (* get_planet_index "Saturn" = Some 5 *)
           split. { reflexivity. } (* get_planet_index "Uranus" = Some 6 *)
           lia. (* 5 < 6 *)
        -- (* j > 1 *) simpl in H_nth_b. discriminate.
    + (* i > 0 *)
      destruct i.
      * (* i = 1, p_a should be "Uranus" *)
        simpl in H_nth_a. injection H_nth_a as H_pa. subst p_a.
        (* Since i=1, j must be > 1 for i < j. But list length is 2. *)
        destruct j; [lia | destruct j; [lia | simpl in H_nth_b; discriminate]].
      * (* i > 1 *)
        simpl in H_nth_a. discriminate.
Qed.