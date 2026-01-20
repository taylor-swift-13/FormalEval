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
Example test_same_chars : same_chars_spec "123445" "" false.
Proof.
  unfold same_chars_spec.
  split.
  - intro H.
    inversion H.
  - intro H.
    specialize (H "1"%char).
    assert (H_in : char_in_string "1"%char "123445").
    { simpl. left. reflexivity. }
    apply H in H_in.
    simpl in H_in.
    contradiction.
Qed.