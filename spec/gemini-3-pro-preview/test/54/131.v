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
Example test_same_chars : same_chars_spec "Sthrong" "0987654321" false.
Proof.
  unfold same_chars_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    specialize (H "S"%char).
    destruct H as [H_fwd _].
    assert (H_in : char_in_string "S" "Sthrong").
    { simpl. left. reflexivity. }
    apply H_fwd in H_in.
    simpl in H_in.
    repeat (destruct H_in as [H_eq | H_in]; [ discriminate | ]).
    contradiction.
Qed.