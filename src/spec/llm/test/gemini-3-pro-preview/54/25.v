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
Example test_same_chars : same_chars_spec "adbbcccddddeeeeehelldefo" "abcde" false.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. inversion H.
  - (* Backward direction: (forall c, ...) -> false = true *)
    intros H.
    (* We prove a contradiction by finding a character in s0 that is not in s1. *)
    (* The character 'h' is present in s0 but not in s1. *)
    assert (Hin: char_in_string "h"%char "adbbcccddddeeeeehelldefo").
    { 
      simpl. 
      (* Automatically search for the character in the list *)
      repeat (try (left; reflexivity); right).
    }
    assert (Hnotin: ~ char_in_string "h"%char "abcde").
    { 
      simpl. 
      intro Hc. 
      (* Prove that 'h' is not equal to any character in "abcde" *)
      repeat (destruct Hc as [Hc | Hc]; [ inversion Hc | ]).
      contradiction.
    }
    (* Use the hypothesis with our counter-example *)
    specialize (H "h"%char).
    destruct H as [Hlr Hrl].
    apply Hlr in Hin.
    contradiction.
Qed.