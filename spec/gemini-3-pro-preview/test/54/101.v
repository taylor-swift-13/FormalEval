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
Example test_same_chars : same_chars_spec "aaabbbccdcd5432cc" "abbabcbc" false.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. inversion H.
  - (* Backward direction: (forall c, ...) -> false = true *)
    intros H.
    (* We show a contradiction by finding a character 'd' in s0 but not s1 *)
    specialize (H "d"%char).
    destruct H as [H1 H2].
    assert (Hin: char_in_string "d"%char "aaabbbccdcd5432cc").
    {
      simpl.
      repeat (try (left; reflexivity); right).
    }
    apply H1 in Hin.
    simpl in Hin.
    repeat (destruct Hin as [H | Hin]; [ inversion H | ]).
    contradiction.
Qed.