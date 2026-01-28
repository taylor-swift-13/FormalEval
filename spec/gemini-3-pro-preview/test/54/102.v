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
Example test_same_chars : same_chars_spec "aabcdbcd" "hlello" false.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: false = true -> ... (contradiction) *)
    intros H.
    inversion H.
  - (* Backward direction: Sets equivalent -> false = true (contradiction) *)
    intros H.
    (* We prove the sets are NOT equivalent by finding a counter-example 'a' *)
    specialize (H "a"%char).
    destruct H as [H_s0_to_s1 _].
    
    (* 'a' is in the first string *)
    assert (H_in_s0 : char_in_string "a" "aabcdbcd").
    { simpl. left. reflexivity. }
    
    (* Therefore 'a' must be in the second string *)
    apply H_s0_to_s1 in H_in_s0.
    
    (* But 'a' is not in "hlello", leading to contradiction *)
    simpl in H_in_s0.
    repeat (destruct H_in_s0 as [H_eq | H_in_s0]; [ inversion H_eq | ]).
    contradiction.
Qed.