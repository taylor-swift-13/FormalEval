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
Example test_same_chars : same_chars_spec "5432cababecdead" "5432cababecdead" true.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: true = true implies the character sets are equivalent *)
    intros _.
    intro c.
    split; intro H.
    + (* Left to Right *)
      assumption.
    + (* Right to Left *)
      assumption.
  - (* Backward direction: The sets are equivalent implies true = true *)
    intros _.
    reflexivity.
Qed.