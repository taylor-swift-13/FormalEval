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
Example test_same_chars : same_chars_spec "abaabde" "a5432caaaabacababecdeadbecdeadbabcbc" false.
Proof.
  unfold same_chars_spec.
  split.
  - intros H. inversion H.
  - intros H.
    specialize (H "c"%char).
    destruct H as [_ H_s1_to_s0].
    assert (H_in_s1 : char_in_string "c"%char "a5432caaaabacababecdeadbecdeadbabcbc").
    { simpl. repeat (try (left; reflexivity); right). }
    apply H_s1_to_s0 in H_in_s1.
    simpl in H_in_s1.
    repeat (destruct H_in_s1 as [H_eq | H_in_s1]; [ inversion H_eq | ]).
    contradiction.
Qed.