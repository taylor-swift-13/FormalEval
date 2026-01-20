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

Example test_bf: bf_spec "Mars" "Earth" [].
Proof.
  unfold bf_spec.
  split.
  - (* Case 1: Prove contradiction if inputs are assumed invalid *)
    intros [H | H].
    + (* Mars is in planets, so ~In is false *)
      exfalso. apply H.
      unfold planets. simpl. tauto.
    + (* Earth is in planets, so ~In is false *)
      exfalso. apply H.
      unfold planets. simpl. tauto.
  - (* Case 2: Prove existence of indices and correct slicing *)
    intros [H1 H2].
    (* Mars is at index 3, Earth is at index 2 *)
    exists 3, 2.
    split.
    + (* Verify index 3 *)
      unfold planets. simpl. reflexivity.
    + split.
      * (* Verify index 2 *)
        unfold planets. simpl. reflexivity.
      * (* Verify the slice logic *)
        (* start = 2, stop = 3 *)
        (* start + 1 = 3 *)
        (* stop - start - 1 = 0 *)
        (* firstn 0 yields [] *)
        unfold planets. simpl. reflexivity.
Qed.