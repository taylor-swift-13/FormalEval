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

Example test_jupiter_neptune : bf_spec "Jupiter" "Neptune" ["Saturn"; "Uranus"].
Proof.
  unfold bf_spec.
  split.
  - (* Case: Both planets are present *)
    intros _.
    exists 4, 7.
    split.
    + (* Verify first index *)
      simpl. reflexivity.
    + split.
      * (* Verify second index *)
        simpl. reflexivity.
      * (* Verify result calculation *)
        simpl. reflexivity.
  - (* Case: One of the planets is missing (Contradiction) *)
    intros [H | H].
    + (* Contradiction: Jupiter is in the list *)
      exfalso. apply H.
      unfold planets. simpl.
      (* Jupiter is at index 4, so we skip 4 disjunctions *)
      do 4 right. left. reflexivity.
    + (* Contradiction: Neptune is in the list *)
      exfalso. apply H.
      unfold planets. simpl.
      (* Neptune is at index 7, so we skip 7 disjunctions *)
      do 7 right. left. reflexivity.
Qed.