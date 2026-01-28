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
Example test_same_chars : same_chars_spec "abbbabcbc54321" "abbbabcbc" false.
Proof.
  unfold same_chars_spec.
  split.
  - intros H. inversion H.
  - intros H.
    exfalso.
    specialize (H "5"%char).
    destruct H as [H1 _].
    assert (HIn : char_in_string "5"%char "abbbabcbc54321").
    { simpl. repeat (try (left; reflexivity); right). }
    apply H1 in HIn.
    simpl in HIn.
    repeat (destruct HIn as [Eq | HIn]; [ inversion Eq | ]).
    contradiction.
Qed.