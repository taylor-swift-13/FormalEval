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
Example test_same_chars : same_chars_spec "5432caaaabacaababbcccddddeeeeecd" "abcd" false.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: false = true implies contradiction *)
    intros H.
    discriminate H.
  - (* Backward direction: The sets are equivalent implies false = true *)
    intros H.
    (* "5" is in the first string but not the second *)
    specialize (H "5"%char).
    destruct H as [H_in_s0 _].
    assert (H_5_in_s0 : char_in_string "5"%char "5432caaaabacaababbcccddddeeeeecd").
    {
      simpl.
      left.
      reflexivity.
    }
    apply H_in_s0 in H_5_in_s0.
    simpl in H_5_in_s0.
    repeat (destruct H_5_in_s0 as [H_eq | H_5_in_s0]; [
      discriminate H_eq
    | ]).
    contradiction.
Qed.