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

Example test_bf: bf_spec "Mercury" "Saturn" ["Venus"; "Earth"; "Mars"; "Jupiter"].
Proof.
  unfold bf_spec.
  split.
  - (* Case 1: Prove contradiction if inputs are assumed invalid *)
    intros [H | H].
    + (* Mercury is in planets, so ~In is false *)
      exfalso. apply H.
      unfold planets. simpl. tauto.
    + (* Saturn is in planets, so ~In is false *)
      exfalso. apply H.
      unfold planets. simpl. tauto.
  - (* Case 2: Prove existence of indices and correct slicing *)
    intros [H1 H2].
    (* Mercury is at index 0, Saturn is at index 5 *)
    exists 0, 5.
    split.
    + (* Verify index 0 *)
      unfold planets. simpl. reflexivity.
    + split.
      * (* Verify index 5 *)
        unfold planets. simpl. reflexivity.
      * (* Verify the slice logic *)
        (* start = 0, stop = 5 *)
        (* start + 1 = 1 *)
        (* stop - start - 1 = 4 *)
        (* skipn 1 planets yields ["Venus"; ...; "Neptune"] *)
        (* firstn 4 yields ["Venus"; "Earth"; "Mars"; "Jupiter"] *)
        unfold planets. simpl. reflexivity.
Qed.