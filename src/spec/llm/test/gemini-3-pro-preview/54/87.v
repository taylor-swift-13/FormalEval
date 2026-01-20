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
Example test_same_chars : same_chars_spec "5432caaaabacaabcd" "cabcd" false.
Proof.
  unfold same_chars_spec.
  split.
  - intros H. discriminate H.
  - intro H.
    (* We need to show that the assumption that the sets are equal leads to a contradiction *)
    (* Pick a character '5' which is in the first string but not the second *)
    specialize (H "5"%char).
    destruct H as [H_s0_implies_s1 _].
    assert (H_in_s0 : char_in_string "5"%char "5432caaaabacaabcd").
    { simpl. left. reflexivity. }
    apply H_s0_implies_s1 in H_in_s0.
    simpl in H_in_s0.
    (* Prove that '5' is not in "cabcd" by exhausting the string *)
    repeat (destruct H_in_s0 as [H_eq | H_in_s0]; [ inversion H_eq | ]).
    contradiction.
Qed.