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
Example test_same_chars : same_chars_spec "" "" true.
Proof.
  unfold same_chars_spec.
  split.
  - intros _.
    intro c.
    split; intro H.
    + simpl in H.
      contradiction.
    + simpl in H.
      contradiction.
  - intros _.
    reflexivity.
Qed.