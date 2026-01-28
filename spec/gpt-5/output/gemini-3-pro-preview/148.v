Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Open Scope string_scope.
Open Scope nat_scope.

Definition planets : list string :=
  ["Mercury"; "Venus"; "Earth"; "Mars"; "Jupiter"; "Saturn"; "Uranus"; "Neptune"].

Definition bf_spec (planet1 planet2 : string) (res : list string) : Prop :=
  (In planet1 planets /\ In planet2 planets ->
    exists i1 i2,
      nth_error planets i1 = Some planet1 /\
      nth_error planets i2 = Some planet2 /\
      res =
        let lo := Nat.min i1 i2 in
        let hi := Nat.max i1 i2 in
        firstn (hi - S lo) (skipn (S lo) planets)) /\
  ((~ In planet1 planets \/ ~ In planet2 planets) -> res = []).

Example test_bf_case : bf_spec "Jupiter" "Neptune" ["Saturn"; "Uranus"].
Proof.
  unfold bf_spec.
  split.
  - (* Case 1: Inputs are valid. Prove existence of indices and result equality. *)
    intros _.
    exists 4, 7.
    split.
    + (* Proof that planets[4] is Jupiter *)
      reflexivity.
    + split.
      * (* Proof that planets[7] is Neptune *)
        reflexivity.
      * (* Proof that the computation matches the result *)
        simpl.
        reflexivity.
  - (* Case 2: Inputs are invalid. Prove contradiction since they are valid. *)
    intros [H_abs | H_abs].
    + (* Contradiction: Jupiter is not in planets *)
      exfalso. apply H_abs.
      unfold planets. simpl.
      (* Search for Jupiter in the list *)
      repeat (try (left; reflexivity); right).
    + (* Contradiction: Neptune is not in planets *)
      exfalso. apply H_abs.
      unfold planets. simpl.
      (* Search for Neptune in the list *)
      repeat (try (left; reflexivity); right).
Qed.