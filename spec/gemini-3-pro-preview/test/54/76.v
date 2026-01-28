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
Example test_same_chars : same_chars_spec "abcdcb5143241a514321de" "abcdeadbbcccddddeeeeehelabdcbabecde" false.
Proof.
  unfold same_chars_spec.
  split.
  - intro H. inversion H.
  - intro H.
    specialize (H "1"%char).
    destruct H as [H1 _].
    assert (H_in : char_in_string "1"%char "abcdcb5143241a514321de").
    { simpl. repeat (try (left; reflexivity); right); try contradiction. }
    apply H1 in H_in.
    simpl in H_in.
    repeat (destruct H_in as [Eq | H_in]; [ inversion Eq | ]).
    contradiction.
Qed.