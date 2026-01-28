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

Fixpoint split_by_space (s : string) : list string :=
  match s with
  | EmptyString => []
  | _ => [] (* placeholder for actual split implementation *)
  end.

Definition parse_music_spec (music_string : string) (result : list Z) : Prop :=
  (music_string = "" -> result = []) /\
  (music_string <> "" ->
    let notes := split_by_space music_string in
    length result = length notes /\
    forall i note beat,
      nth_error notes i = Some note ->
      nth_error result i = Some beat ->
      ((note = "o" /\ beat = 4) \/
       (note = "o|" /\ beat = 2) \/
       (note = ".|" /\ beat = 1))).

Example test_parse_music_empty: parse_music_spec "" [].
Proof.
  unfold parse_music_spec.
  split.
  - (* Case: music_string = "" *)
    intros H.
    reflexivity.
  - (* Case: music_string <> "" *)
    intros H.
    (* H : "" <> "" implies False *)
    contradiction H.
    reflexivity.
Qed.