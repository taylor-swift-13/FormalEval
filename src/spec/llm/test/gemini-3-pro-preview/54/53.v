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
Example test_same_chars : same_chars_spec "abbbabcbc" "1234545" false.
Proof.
  unfold same_chars_spec.
  split.
  - intros H. inversion H.
  - intros H.
    specialize (H "a"%char).
    destruct H as [H1 H2].
    assert (H3 : char_in_string "a"%char "abbbabcbc").
    { simpl. left. reflexivity. }
    apply H1 in H3.
    simpl in H3.
    repeat (destruct H3 as [H3 | H3]; [ inversion H3 | ]).
    contradiction.
Qed.