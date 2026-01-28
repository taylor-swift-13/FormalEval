Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

Definition planets : list string :=
  ["Mercury"; "Venus"; "Earth"; "Mars"; "Jupiter"; "Saturn"; "Uranus"; "Neptune"].

Definition bf_spec (planet1 planet2 : string) (result : list string) : Prop :=
  let valid_p1 := In planet1 planets in
  let valid_p2 := In planet2 planets in
  
  (~ valid_p1 \/ ~ valid_p2 -> result = []) /\
  (valid_p1 /\ valid_p2 ->
    exists i1 i2,
      nth_error planets i1 = Some planet1 /\
      nth_error planets i2 = Some planet2 /\
      let start := Nat.min i1 i2 in
      let stop := Nat.max i1 i2 in
      (* Corresponds to python slice planets[start + 1 : stop] *)
      result = firstn (stop - start - 1) (skipn (start + 1) planets)).

Example test_bf: bf_spec "Uranus" "Jupiter" ["Saturn"].
Proof.
  unfold bf_spec.
  split.
  - (* Case 1: Prove contradiction if inputs are assumed invalid *)
    intros [H | H].
    + (* Uranus is in planets, so ~In is false *)
      exfalso. apply H.
      unfold planets. simpl. tauto.
    + (* Jupiter is in planets, so ~In is false *)
      exfalso. apply H.
      unfold planets. simpl. tauto.
  - (* Case 2: Prove existence of indices and correct slicing *)
    intros [H1 H2].
    (* Uranus is at index 6, Jupiter is at index 4 *)
    exists 6, 4.
    split.
    + (* Verify index 6 *)
      unfold planets. simpl. reflexivity.
    + split.
      * (* Verify index 4 *)
        unfold planets. simpl. reflexivity.
      * (* Verify the slice logic *)
        (* start = 4, stop = 6 *)
        (* start + 1 = 5 *)
        (* stop - start - 1 = 1 *)
        (* skipn 5 planets yields ["Saturn"; "Uranus"; "Neptune"] *)
        (* firstn 1 yields ["Saturn"] *)
        unfold planets. simpl. reflexivity.
Qed.