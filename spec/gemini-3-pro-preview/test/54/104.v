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
Example test_same_chars : same_chars_spec "abbbabcbc" "1234123445545" false.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: false = true implies contradiction *)
    intros H.
    inversion H.
  - (* Backward direction: The sets are equivalent implies false = true *)
    intros H.
    (* We show the sets are not equivalent to derive a contradiction. *)
    (* Specialize the hypothesis with 'a', which is in the first string but not the second. *)
    specialize (H "a"%char).
    destruct H as [H1 _].
    assert (HIn : char_in_string "a"%char "abbbabcbc").
    { simpl. left. reflexivity. }
    apply H1 in HIn.
    simpl in HIn.
    (* 'a' cannot be equal to any character in the second string. *)
    repeat (destruct HIn as [Heq | HIn]; [ discriminate Heq | ]).
    contradiction.
Qed.