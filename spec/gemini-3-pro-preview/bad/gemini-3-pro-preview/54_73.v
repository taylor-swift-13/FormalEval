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
Example test_same_chars : same_chars_spec "aabcdcbadcbade" "aabcdefgb" false.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: false = true implies ... *)
    intro H.
    discriminate H.
  - (* Backward direction: The sets are equivalent implies false = true *)
    intro H.
    (* We show a contradiction by finding a character 'f' in s1 but not s0 *)
    specialize (H "f"%char).
    destruct H as [_ H_s1_implies_s0].
    
    (* Prove 'f' is in s1 *)
    assert (H_in_s1 : char_in_string "f"%char "aabcdefgb").
    { 
      simpl. 
      repeat (try (left; reflexivity); right). 
      contradiction. 
    }
    
    (* Apply the equivalence to show 'f' must be in s0 *)
    apply H_s1_implies_s0 in H_in_s1.
    
    (* Show 'f' is NOT in s0 to derive contradiction *)
    simpl in H_in_s1.
    repeat (destruct H_in_s1 as [H_eq | H_in_s1]; [ inversion H_eq; discriminate | ]).
    contradiction.
Qed.