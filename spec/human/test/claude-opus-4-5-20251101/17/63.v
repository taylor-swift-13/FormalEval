Require Import Ascii String List.
Import ListNotations.
Open Scope string_scope.

Fixpoint SplitOnSpaces_aux (current_group : list ascii) (S : string) : list string :=
  match S with
  | EmptyString =>
    match current_group with
    | [] => []
    | _ => [string_of_list_ascii (List.rev current_group)]
    end
  | String h t =>
    if ascii_dec h " "%char then
      match current_group with
      | [] => SplitOnSpaces_aux [] t
      | _ => (string_of_list_ascii (List.rev current_group)) :: SplitOnSpaces_aux [] t
      end
    else
      SplitOnSpaces_aux (h :: current_group) t
  end.

Definition SplitOnSpaces (S : string) : list string :=
  SplitOnSpaces_aux [] S.

Definition parse_note (note : string) : option nat :=
  if string_dec note "o" then Some 4
  else if string_dec note "o|" then Some 2
  else if string_dec note ".|" then Some 1
  else None.

Fixpoint parse_music_impl_aux (notes : list string) : list nat :=
  match notes with
  | [] => []
  | note :: rest =>
    match parse_note note with
    | Some n => n :: parse_music_impl_aux rest
    | None => parse_music_impl_aux rest
    end
  end.

Definition parse_music_impl (input : string) : list nat :=
  parse_music_impl_aux (SplitOnSpaces input).

Definition problem_17_pre (input : string) : Prop := True.

Definition problem_17_spec (input : string) (output : list nat) : Prop :=
  output = parse_music_impl input.

Example test_music : problem_17_spec "o| .| o| o| o| o|" [2; 1; 2; 2; 2; 2].
Proof.
  unfold problem_17_spec.
  unfold parse_music_impl.
  unfold SplitOnSpaces.
  simpl.
  reflexivity.
Qed.