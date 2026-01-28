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
Example test_same_chars : same_chars_spec "abcdcbadcbade" "abbc" false.
Proof.
  unfold same_chars_spec.
  split.
  - intro H. inversion H.
  - intro H.
    specialize (H "d"%char).
    assert (Hin : char_in_string "d"%char "abcdcbadcbade").
    { simpl. repeat (try (left; reflexivity); right). }
    apply H in Hin.
    simpl in Hin.
    repeat (destruct Hin as [Contra | Hin]; [ inversion Contra | ]).
    contradiction.
Qed.