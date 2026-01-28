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
Example test_same_chars : same_chars_spec "5432caaaababecdead" "aabcdbcd" false.
Proof.
  unfold same_chars_spec.
  split.
  - (* Forward direction: false = true -> ... *)
    intros H.
    inversion H.
  - (* Backward direction: equivalent sets -> false = true *)
    intros H.
    (* The sets are not equivalent because '5' is in the first string but not the second. *)
    (* '5' corresponds to ascii_of_nat 53 *)
    specialize (H (Ascii.ascii_of_nat 53)).
    destruct H as [H1 _].
    assert (HIn : char_in_string (Ascii.ascii_of_nat 53) "5432caaaababecdead").
    { simpl. left. reflexivity. }
    apply H1 in HIn.
    simpl in HIn.
    (* Verify '5' is not in "aabcdbcd" by exhausting the disjunctions *)
    repeat (destruct HIn as [HIn | HIn]; [ inversion HIn | ]).
    contradiction.
Qed.