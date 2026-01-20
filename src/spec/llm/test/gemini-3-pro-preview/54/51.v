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
Example test_same_chars : same_chars_spec "aab" "cd" false.
Proof.
  unfold same_chars_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    (* We need to show that the assumption that the sets are equal leads to a contradiction. *)
    (* "a" is in "aab" but not in "cd". *)
    specialize (H "a"%char).
    assert (Hin : char_in_string "a"%char "aab").
    { simpl. left. reflexivity. }
    apply H in Hin.
    simpl in Hin.
    (* Hin now states that 'a' is in "cd", which is false. *)
    repeat (destruct Hin as [Heq | Hin]; [ discriminate Heq | ]).
    contradiction.
Qed.