Require Import Ascii String List ZArith.
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

Definition parse_note (note : string) : option Z :=
  if string_dec note "o" then Some 4%Z
  else if string_dec note "o|" then Some 2%Z
  else if string_dec note ".|" then Some 1%Z
  else None.

Fixpoint parse_music_impl_aux (notes : list string) : list Z :=
  match notes with
  | [] => []
  | note :: rest =>
    match parse_note note with
    | Some n => n :: parse_music_impl_aux rest
    | None => parse_music_impl_aux rest
    end
  end.

Definition parse_music_impl (input : string) : list Z :=
  parse_music_impl_aux (SplitOnSpaces input).

Definition problem_17_pre (input : string) : Prop := True.

Definition problem_17_spec (input : string) (output : list Z) : Prop :=
  output = parse_music_impl input.

Example test_case_2 : problem_17_spec "o| o o| o o| o| o|" [2%Z; 4%Z; 2%Z; 4%Z; 2%Z; 2%Z; 2%Z].
Proof.
  unfold problem_17_spec.
  unfold parse_music_impl.
  simpl.
  reflexivity.
Qed.