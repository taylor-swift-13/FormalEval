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
Example test_same_chars : same_chars_spec "524321" "5432" false.
Proof.
  unfold same_chars_spec.
  split.
  - intros H. inversion H.
  - intros H.
    specialize (H "1"%char).
    destruct H as [H1 H2].
    assert (Hin: char_in_string "1"%char "524321").
    { simpl. repeat (try (left; reflexivity); right). }
    apply H1 in Hin.
    simpl in Hin.
    repeat match goal with
    | [ H : _ \/ _ |- _ ] => destruct H as [Heq | H]; [ inversion Heq | ]
    end.
    contradiction.
Qed.