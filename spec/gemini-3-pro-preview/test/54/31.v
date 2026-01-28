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
Example test_same_chars : same_chars_spec "ab54321fg" "gfedcba" false.
Proof.
  unfold same_chars_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    specialize (H "1"%char).
    destruct H as [H_in_s0 _].
    assert (H1_in_s0 : char_in_string "1"%char "ab54321fg").
    {
      simpl.
      repeat (try (left; reflexivity); right).
    }
    apply H_in_s0 in H1_in_s0.
    simpl in H1_in_s0.
    repeat (destruct H1_in_s0 as [H_eq | H1_in_s0]; [ discriminate | ]).
    contradiction.
Qed.