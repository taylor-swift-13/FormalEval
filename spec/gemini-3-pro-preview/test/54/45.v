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
Example test_same_chars : same_chars_spec "abcdcb5143241a514321de" "abcdcbadcbade" false.
Proof.
  unfold same_chars_spec.
  split.
  - intros H. inversion H.
  - intros H.
    specialize (H "1"%char).
    destruct H as [H_in _].
    assert (H_exists : char_in_string "1"%char "abcdcb5143241a514321de").
    {
      simpl.
      repeat (try (left; reflexivity); right).
    }
    apply H_in in H_exists.
    simpl in H_exists.
    repeat (destruct H_exists as [H_eq | H_exists]; [ inversion H_eq | ]).
    contradiction.
Qed.