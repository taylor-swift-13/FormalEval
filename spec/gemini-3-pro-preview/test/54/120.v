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
Example test_same_chars : same_chars_spec "tacocspeGod!e Amaze a stunning, gorgeous, bewitching, and dazzling specter of my dear gazelle!cterat" "tacocspecterat" false.
Proof.
  unfold same_chars_spec.
  split.
  - intro H. inversion H.
  - intro H.
    specialize (H "G"%char).
    destruct H as [H_impl _].
    assert (H_in : char_in_string "G"%char "tacocspeGod!e Amaze a stunning, gorgeous, bewitching, and dazzling specter of my dear gazelle!cterat").
    { simpl. repeat (try (left; reflexivity); right). }
    apply H_impl in H_in.
    simpl in H_in.
    repeat (destruct H_in as [H_eq | H_in]; [ discriminate | ]).
    contradiction.
Qed.