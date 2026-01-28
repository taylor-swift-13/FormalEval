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
Example test_same_chars : same_chars_spec "5432caaaabacaababbcccddddeeeeecd" "abcabcdcb5143241a514321db" false.
Proof.
  unfold same_chars_spec.
  split.
  - intro H. discriminate.
  - intro H.
    specialize (H "e"%char).
    destruct H as [H_in_s0_implies_s1 _].
    assert (H_in_s0 : char_in_string "e"%char "5432caaaabacaababbcccddddeeeeecd").
    { simpl. repeat (try (left; reflexivity); right). }
    apply H_in_s0_implies_s1 in H_in_s0.
    simpl in H_in_s0.
    repeat (destruct H_in_s0 as [H_eq | H_in_s0]; [ discriminate | ]).
    contradiction.
Qed.