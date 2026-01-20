Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

(* Specification Definitions *)
Fixpoint char_in_string (c : ascii) (s : string) : Prop :=
  match s with
  | EmptyString => False
  | String c' s' => c = c' \/ char_in_string c s'
  end.

Definition same_chars_spec (s0 s1 : string) (result : bool) : Prop :=
  result = true <-> (forall c : ascii, char_in_string c s0 <-> char_in_string c s1).

(* Test Case Proof *)
Example test_same_chars : same_chars_spec "abcd" "aabcdbcd" true.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction *)
    intros _.
    intro c.
    split; intro H.
    + (* Left to Right *)
      simpl in H.
      repeat (destruct H as [H | H]; [
        subst c;
        simpl;
        repeat (try (left; reflexivity); right);
        try contradiction
      | ]).
      contradiction.
      
    + (* Right to Left *)
      simpl in H.
      repeat (destruct H as [H | H]; [
        subst c;
        simpl;
        repeat (try (left; reflexivity); right);
        try contradiction
      | ]).
      contradiction.

  - (* Backward direction *)
    intros _.
    reflexivity.
Qed.