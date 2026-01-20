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
Example test_same_chars : same_chars_spec "ab" "cbad" false.
Proof.
  unfold same_chars_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    specialize (H "c"%char).
    destruct H as [_ H].
    assert (H_in : char_in_string "c"%char "cbad").
    { simpl. left. reflexivity. }
    apply H in H_in.
    simpl in H_in.
    destruct H_in as [H1 | [H2 | H3]].
    + inversion H1.
    + inversion H2.
    + contradiction.
Qed.