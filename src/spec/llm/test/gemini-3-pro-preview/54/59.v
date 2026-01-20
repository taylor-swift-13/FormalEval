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
Example test_same_chars : same_chars_spec "llohelldefo" "llo" false.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: false = true implies anything *)
    intros H.
    inversion H.
  - (* Backward direction: The sets are equivalent implies false = true *)
    intros H.
    (* We need to show False. We find a character in s0 that is not in s1. *)
    (* 'h' is in "llohelldefo" but not in "llo" *)
    specialize (H "h"%char).
    destruct H as [H_in_s0 H_in_s1].
    
    (* Prove 'h' is in "llohelldefo" *)
    assert (Hin: char_in_string "h"%char "llohelldefo").
    { 
      simpl. 
      repeat (try (left; reflexivity); right);
      try contradiction. 
    }
    
    (* Apply the equivalence to deduce 'h' must be in "llo" *)
    apply H_in_s0 in Hin.
    
    (* Prove 'h' is NOT in "llo" to derive contradiction *)
    simpl in Hin.
    repeat (destruct Hin as [H_eq | Hin]; [ inversion H_eq | ]);
    try contradiction.
Qed.