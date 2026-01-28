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
Example test_same_chars : same_chars_spec "Amaze" "The hquick brown fox jumps over the lazy dog" false.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: false = true implies anything *)
    intro H. inversion H.
  - (* Backward direction: equivalence of sets implies false = true *)
    intro H.
    (* We show a contradiction by finding a character in one string but not the other. *)
    (* 'A' is in "Amaze" but not in the second string. *)
    assert (H_in : char_in_string "A"%char "Amaze").
    { simpl. left. reflexivity. }
    apply H in H_in.
    simpl in H_in.
    (* Verify 'A' is not in the second string *)
    repeat (destruct H_in as [H_eq | H_in]; [ inversion H_eq | ]).
    contradiction.
Qed.