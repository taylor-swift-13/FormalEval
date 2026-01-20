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

Example test_bf: bf_spec "MercuNeptunMarsery" "Neptune" [].
Proof.
  unfold bf_spec.
  split.
  - (* Case 1: One of the inputs is invalid, so result must be empty *)
    intros _.
    reflexivity.
  - (* Case 2: If both were valid (contradiction) *)
    intros [H1 H2].
    unfold planets in H1.
    simpl in H1.
    (* H1 states that "MercuNeptunMarsery" is in the list, which is false *)
    repeat (destruct H1; try discriminate).
Qed.