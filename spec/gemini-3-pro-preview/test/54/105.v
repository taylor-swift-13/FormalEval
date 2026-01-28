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
Example test_same_chars : same_chars_spec "abcdeadbbcccddddeeeeehelldefogfedcba" "abbhelleoc" false.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: false = true -> ... (contradiction) *)
    intros H. inversion H.
  - (* Backward direction: The sets are equivalent -> false = true *)
    intros H.
    (* We prove the sets are NOT equivalent by finding a counter-example *)
    (* 'd' is in the first string but not the second *)
    specialize (H "d"%char).
    destruct H as [H_s0_to_s1 _].
    
    (* Prove 'd' is in s0 *)
    assert (Hin_s0 : char_in_string "d"%char "abcdeadbbcccddddeeeeehelldefogfedcba").
    { simpl. repeat (try (left; reflexivity); right). }
    
    (* Apply the hypothesis to deduce 'd' must be in s1 *)
    apply H_s0_to_s1 in Hin_s0.
    
    (* Prove 'd' is NOT in s1 to derive contradiction *)
    simpl in Hin_s0.
    repeat (destruct Hin_s0 as [Heq | Hin_s0]; [ inversion Heq | ]).
    contradiction.
Qed.