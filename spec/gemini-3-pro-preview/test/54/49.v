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
Example test_same_chars : same_chars_spec "abcdeadbbcccddddeeeeehelabdcba" "54321" false.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: false = true implies contradiction *)
    intro H. discriminate H.
  - (* Backward direction: The sets are equivalent implies false = true *)
    intro H.
    (* We show the hypothesis H leads to a contradiction because the sets are not equivalent. *)
    (* Specifically, 'a' is in the first string but not the second. *)
    specialize (H "a"%char).
    destruct H as [H_lr _].
    
    (* Prove 'a' is in the first string *)
    assert (H_in : char_in_string "a"%char "abcdeadbbcccddddeeeeehelabdcba").
    { simpl. left. reflexivity. }
    
    (* Use the hypothesis to deduce 'a' must be in the second string *)
    apply H_lr in H_in.
    
    (* Show that 'a' being in "54321" is a contradiction *)
    simpl in H_in.
    repeat (destruct H_in as [H_contra | H_in]; [ discriminate H_contra | ]).
    contradiction.
Qed.