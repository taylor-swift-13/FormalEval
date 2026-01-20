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

Example bf_spec_test_Jupiter_Neptune :
  bf_spec "Jupiter" "Neptune" ["Saturn"; "Uranus"].
Proof.
  unfold bf_spec.
  simpl.
  split.
  - intros Hinv.
    assert (In "Jupiter" planets) as v1.
    { simpl. right. right. right. right. left. reflexivity. }
    assert (In "Neptune" planets) as v2.
    { simpl. right. right. right. right. right. right. right. left. reflexivity. }
    destruct Hinv as [Hnj | Hnn].
    + exfalso. apply Hnj. exact v1.
    + exfalso. apply Hnn. exact v2.
  - intros [Hv1 Hv2].
    exists 4, 7.
    split.
    + simpl. reflexivity.
    + split.
      * simpl. reflexivity.
      * simpl. reflexivity.
Qed.