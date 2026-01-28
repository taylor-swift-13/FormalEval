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
Example test_same_chars : same_chars_spec "aaa" "aaaa" true.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: true = true implies the character sets are equivalent *)
    intros _.
    intro c.
    split; intro H.
    + (* Left to Right: c in "aaa" -> c in "aaaa" *)
      simpl in H.
      (* Destruct the hypothesis for every character in the first string *)
      repeat (destruct H as [H | H]; [
        subst c; (* Replace c with the specific character *)
        simpl;   (* Unfold char_in_string for the target string *)
        (* Attempt to find the character in the target disjunction *)
        repeat (try (left; reflexivity); right);
        try contradiction (* Fallback *)
      | ]).
      contradiction. (* Base case of EmptyString in hypothesis *)
      
    + (* Right to Left: c in "aaaa" -> c in "aaa" *)
      simpl in H.
      (* Destruct the hypothesis for every character in the second string *)
      repeat (destruct H as [H | H]; [
        subst c;
        simpl;
        repeat (try (left; reflexivity); right);
        try contradiction
      | ]).
      contradiction.

  - (* Backward direction: The sets are equivalent implies true = true *)
    intros _.
    reflexivity.
Qed.