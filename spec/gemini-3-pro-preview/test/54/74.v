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
Example test_same_chars : same_chars_spec "llaaa1234a5bbbccco" "llo" false.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. inversion H.
  - (* Backward direction: (forall c, ...) -> false = true *)
    intros H.
    (* Counterexample: 'a' is in s0 but not in s1 *)
    pose (c := Ascii.ascii_of_nat 97).
    assert (H_in : char_in_string c "llaaa1234a5bbbccco").
    { simpl. repeat (try (left; reflexivity); right). }
    apply H in H_in.
    simpl in H_in.
    repeat (destruct H_in as [H_contra | H_in]; [ inversion H_contra | ]).
    contradiction.
Qed.