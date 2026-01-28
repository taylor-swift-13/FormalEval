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
Example test_same_chars : same_chars_spec "aabcdefgbcdeadbbcccabcdeadbbcccddddee5432caaaabacaabcdehelabdcbaa" "abcdeadbbcccabcdeadbbcccddddeeeeehelabdcbaa" false.
Proof.
  unfold same_chars_spec.
  split.
  - intros H. discriminate.
  - intros H.
    specialize (H "5"%char).
    destruct H as [H_s0_s1 _].
    assert (H_in_s0 : char_in_string "5"%char "aabcdefgbcdeadbbcccabcdeadbbcccddddee5432caaaabacaabcdehelabdcbaa").
    {
      simpl.
      repeat (try (left; reflexivity); right).
    }
    apply H_s0_s1 in H_in_s0.
    simpl in H_in_s0.
    repeat (destruct H_in_s0 as [H_eq | H_in_s0]; [ inversion H_eq | ]).
    contradiction.
Qed.