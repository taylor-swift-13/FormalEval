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

Example test_bf: bf_spec "Venus" "Mars" ["Earth"].
Proof.
  unfold bf_spec.
  split.
  - (* Case 1: Prove contradiction if inputs are assumed invalid *)
    intros [H | H].
    + (* Venus is in planets, so ~In is false *)
      exfalso. apply H.
      unfold planets. simpl. tauto.
    + (* Mars is in planets, so ~In is false *)
      exfalso. apply H.
      unfold planets. simpl. tauto.
  - (* Case 2: Prove existence of indices and correct slicing *)
    intros [H1 H2].
    (* Venus is at index 1, Mars is at index 3 *)
    exists 1, 3.
    split.
    + (* Verify index 1 *)
      unfold planets. simpl. reflexivity.
    + split.
      * (* Verify index 3 *)
        unfold planets. simpl. reflexivity.
      * (* Verify the slice logic *)
        (* start = 1, stop = 3 *)
        (* start + 1 = 2 *)
        (* stop - start - 1 = 1 *)
        (* skipn 2 planets yields ["Earth"; "Mars"; ...] *)
        (* firstn 1 yields ["Earth"] *)
        unfold planets. simpl. reflexivity.
Qed.