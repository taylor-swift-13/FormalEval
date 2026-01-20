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

Example bf_test_jupiter_neptune : bf_spec "Jupiter" "Neptune" ["Saturn"; "Uranus"].
Proof.
  unfold bf_spec.
  split.
  - (* Case: invalid planets -> result = [] *)
    intros H.
    destruct H as [H | H].
    + (* Jupiter is not valid - contradiction *)
      exfalso.
      apply H.
      unfold planets.
      simpl.
      right. right. right. right. left. reflexivity.
    + (* Neptune is not valid - contradiction *)
      exfalso.
      apply H.
      unfold planets.
      simpl.
      right. right. right. right. right. right. right. left. reflexivity.
  - (* Case: both valid -> exists indices *)
    intros [H1 H2].
    (* Jupiter is at index 4, Neptune is at index 7 *)
    exists 4, 7.
    split.
    + (* nth_error planets 4 = Some "Jupiter" *)
      simpl. reflexivity.
    + split.
      * (* nth_error planets 7 = Some "Neptune" *)
        simpl. reflexivity.
      * (* result = firstn (7 - 4 - 1) (skipn (4 + 1) planets) *)
        (* start = min 4 7 = 4, stop = max 4 7 = 7 *)
        (* result = firstn (7 - 4 - 1) (skipn 5 planets) *)
        (* result = firstn 2 (skipn 5 planets) *)
        simpl.
        reflexivity.
Qed.