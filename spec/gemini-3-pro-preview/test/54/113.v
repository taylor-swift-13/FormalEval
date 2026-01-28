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
Example test_same_chars : same_chars_spec "The quick brown fox jumps over the lazy dog" "God! Amaze a stunning, gorgeous, bewitching, and dazzling specter of my dear gazelle!" false.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: false = true -> ... (contradiction) *)
    intros H. inversion H.
  - (* Backward direction: ... -> false = true (contradiction) *)
    intros H.
    (* The hypothesis H claims the character sets are identical.
       We disprove this by finding a character 'T' in the first string but not the second. *)
    specialize (H "T"%char).
    destruct H as [H_s0_to_s1 _].
    
    (* Prove 'T' is in s0 *)
    assert (H_in_s0 : char_in_string "T"%char "The quick brown fox jumps over the lazy dog").
    { simpl. left. reflexivity. }
    
    (* Apply the hypothesis to show 'T' must be in s1 *)
    apply H_s0_to_s1 in H_in_s0.
    
    (* Show 'T' is NOT in s1 to derive contradiction *)
    simpl in H_in_s0.
    repeat match goal with
    | [ H : _ = _ \/ _ |- _ ] => destruct H as [H | H]; [ discriminate | ]
    | [ H : False |- _ ] => contradiction
    end.
Qed.