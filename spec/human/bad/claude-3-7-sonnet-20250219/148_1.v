Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
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

Definition problem_148_spec (planet1 planet2 : string) (result : list string) : Prop :=
  match (get_planet_index planet1), (get_planet_index planet2) with
  | Some idx1, Some idx2 =>
    let min_idx := Nat.min idx1 idx2 in
    let max_idx := Nat.max idx1 idx2 in
    (forall p, In p result <->
      (exists idx, get_planet_index p = Some idx /\ min_idx < idx < max_idx))
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

Example bf_jupiter_neptune_correct :
  problem_148_spec "Jupiter" "Neptune" ["Saturn"; "Uranus"].
Proof.
  unfold problem_148_spec.
  (* Evaluate indices *)
  remember (get_planet_index "Jupiter") as idx1 eqn:Eidx1.
  remember (get_planet_index "Neptune") as idx2 eqn:Eidx2.

  (* Simplify and compute the indices *)
  unfold get_planet_index in Eidx1, Eidx2.
  vm_compute in Eidx1.
  inversion Eidx1; subst idx1; clear Eidx1.
  vm_compute in Eidx2.
  inversion Eidx2; subst idx2; clear Eidx2.
  (* idx1 = Some 4, idx2 = Some 7 *)

  simpl.
  split.
  - intros p.
    split.
    + intros Hin.
      simpl in Hin.
      destruct Hin as [Hsat | [Hura | Hf]]; try contradiction.
      * exists 5.
        split.
        -- vm_compute. reflexivity.
        -- lia.
      * exists 6.
        split.
        -- vm_compute. reflexivity.
        -- lia.
    + intros [idx [Hget Hbound]].
      assert (idx = 5 \/ idx = 6) by lia.
      destruct H as [H5 | H6].
      * subst idx.
        rewrite Hget.
        left.
        vm_compute. reflexivity.
      * subst idx.
        rewrite Hget.
        right.
        left.
        vm_compute. reflexivity.
  - intros p_a p_b i j Hi Hj Hij.
    destruct i; destruct j.
    + lia. (* i=0, j=0 impossible i < j *)
    + simpl in Hi, Hj.
      inversion Hi; subst p_a.
      inversion Hj; subst p_b.
      exists 5, 6.
      repeat split; vm_compute; lia.
    + lia. (* i=1, j=0 impossible i < j *)
    + lia. (* i=1, j=1 impossible i < j *)
Qed.