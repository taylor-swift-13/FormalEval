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
Example test_same_chars : same_chars_spec "5432cabecdead" "5432cababecdead" true.
Proof.
  unfold same_chars_spec.
  split.
  - intros _.
    intro c.
    split; intro H.
    + simpl in H.
      repeat (destruct H as [H | H]; [
        subst c;
        simpl;
        repeat (try (left; reflexivity); right);
        try contradiction
      | ]).
      contradiction.
      
    + simpl in H.
      repeat (destruct H as [H | H]; [
        subst c;
        simpl;
        repeat (try (left; reflexivity); right);
        try contradiction
      | ]).
      contradiction.

  - intros _.
    reflexivity.
Qed.