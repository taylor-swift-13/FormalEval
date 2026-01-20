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
Example test_same_chars : same_chars_spec "aaabbbccc" "a5432caaaabacababecdeadbecdeadbabcbc" false.
Proof.
  unfold same_chars_spec.
  split.
  - intros H. inversion H.
  - intros H.
    specialize (H (ascii_of_nat 53)).
    destruct H as [_ H].
    assert (H_in : char_in_string (ascii_of_nat 53) "a5432caaaabacababecdeadbecdeadbabcbc").
    { simpl. right. left. reflexivity. }
    apply H in H_in.
    simpl in H_in.
    repeat (destruct H_in as [H_eq | H_in]; [ inversion H_eq | ]).
    contradiction.
Qed.