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
Example test_same_chars : same_chars_spec "cd" "abcd" false.
Proof.
  unfold same_chars_spec.
  split.
  - intro H. discriminate.
  - intro H.
    assert (Ha : char_in_string "a"%char "abcd").
    { simpl. left. reflexivity. }
    specialize (H "a"%char).
    destruct H as [_ H].
    apply H in Ha.
    simpl in Ha.
    repeat destruct Ha as [Ha | Ha]; try discriminate; try contradiction.
Qed.