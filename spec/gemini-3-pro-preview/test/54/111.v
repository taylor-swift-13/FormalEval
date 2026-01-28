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
Example test_same_chars : same_chars_spec "ZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZe" "ezzzezezezezezezeeeezezezezezezezeeee" false.
Proof.
  unfold same_chars_spec.
  split.
  - intros H. inversion H.
  - intro H.
    assert (Hin : char_in_string "Z"%char "ZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZeZe").
    { simpl. left. reflexivity. }
    apply H in Hin.
    simpl in Hin.
    repeat (destruct Hin as [Heq | Hin]; [ inversion Heq | ]).
    contradiction.
Qed.