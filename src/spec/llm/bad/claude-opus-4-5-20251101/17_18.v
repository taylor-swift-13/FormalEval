Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Definition count_beats (note : string) : option Z :=
  if string_dec note "o" then Some 4
  else if string_dec note "o|" then Some 2
  else if string_dec note ".|" then Some 1
  else None.

Definition split_by_space (s : string) : list string :=
  match s with
  | EmptyString => []
  | _ => []
  end.

Definition parse_music_spec (music_string : string) (result : list Z) : Prop :=
  forall i beat,
    nth_error result i = Some beat ->
    (beat = 4 \/ beat = 2 \/ beat = 1).

Example parse_music_test_notes : parse_music_spec "o| o| o| o| .| .| .|" [2%Z; 2%Z; 2%Z; 2%Z; 1%Z; 1%Z; 1%Z].
Proof.
  unfold parse_music_spec.
  intros i beat H.
  destruct i as [|[|[|[|[|[|[|]]]]]]]; simpl in H; inversion H; auto.
Qed.