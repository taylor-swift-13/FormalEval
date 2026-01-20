Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.

Fixpoint char_in_string (c : ascii) (s : string) : Prop :=
  match s with
  | EmptyString => False
  | String c' s' => c = c' \/ char_in_string c s'
  end.

Definition same_chars_spec (s0 s1 : string) (result : bool) : Prop :=
  result = true <-> (forall c : ascii, char_in_string c s0 <-> char_in_string c s1).

(* Characters in "eabcdzzzz": e, a, b, c, d, z *)
(* Characters in "dddzzzzzzzddeddabc": d, z, e, a, b, c *)
(* Both strings have exactly the same set of characters: {a, b, c, d, e, z} *)

Example test_same_chars : same_chars_spec "eabcdzzzz"%string "dddzzzzzzzddeddabc"%string true.
Proof.
  unfold same_chars_spec.
  split.
  - intros _. intros c.
    split; intros H.
    + (* char_in_string c "eabcdzzzz" -> char_in_string c "dddzzzzzzzddeddabc" *)
      simpl in H.
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]];
      subst; simpl;
      try (left; reflexivity);
      try (right; left; reflexivity);
      try (right; right; left; reflexivity);
      try (right; right; right; left; reflexivity);
      try (right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity);
      try contradiction.
    + (* char_in_string c "dddzzzzzzzddeddabc" -> char_in_string c "eabcdzzzz" *)
      simpl in H.
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]];
      subst; simpl;
      try (left; reflexivity);
      try (right; left; reflexivity);
      try (right; right; left; reflexivity);
      try (right; right; right; left; reflexivity);
      try (right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; right; left; reflexivity);
      try (right; right; right; right; right; right; right; right; left; reflexivity);
      try contradiction.
  - intros _. reflexivity.
Qed.