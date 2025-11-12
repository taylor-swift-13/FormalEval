(* """ Input to this function is a string representing musical notes in a special ASCII format.
Your task is to parse this string and return list of integers corresponding to how many beats does each
not last.

Here is a legend:
'o' - whole note, lasts four beats
'o|' - half note, lasts two beats
'.|' - quater note, lasts one beat

>>> parse_music('o o| .| o| o| .| .| .| .| o o')
[4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4]
""" *)

Require Import Ascii String List.
Import ListNotations.

Inductive SplitOnSpaces_aux_rel : list ascii -> list ascii -> list (list ascii) -> Prop :=
  | sosar_nil_empty : forall current_group, current_group = [] -> SplitOnSpaces_aux_rel current_group [] []
  | sosar_nil_nonempty : forall current_group, current_group <> [] -> SplitOnSpaces_aux_rel current_group [] [List.rev current_group]
  | sosar_space_empty : forall current_group h t result,
      h = " "%char ->
      current_group = [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (h :: t) result
  | sosar_space_nonempty : forall current_group h t result,
      h = " "%char ->
      current_group <> [] ->
      SplitOnSpaces_aux_rel [] t result ->
      SplitOnSpaces_aux_rel current_group (h :: t) ((List.rev current_group) :: result)
  | sosar_char : forall current_group h t result,
      h <> " "%char ->
      SplitOnSpaces_aux_rel (h :: current_group) t result ->
      SplitOnSpaces_aux_rel current_group (h :: t) result.

Inductive SplitOnSpaces_rel : list ascii -> list (list ascii) -> Prop :=
  | sos_base : forall S result, SplitOnSpaces_aux_rel [] S result -> SplitOnSpaces_rel S result.

Inductive parse_note_rel : list ascii -> nat -> Prop :=
  | pnr_whole : parse_note_rel ["o"%char] 4
  | pnr_half : parse_note_rel ["o"%char; "|"%char] 2
  | pnr_quarter : parse_note_rel ["."%char; "|"%char] 1.

Inductive parse_music_impl_aux_rel : list (list ascii) -> list nat -> Prop :=
  | pmiar_nil : parse_music_impl_aux_rel [] []
  | pmiar_cons : forall note rest beats beat,
      parse_note_rel note beat ->
      parse_music_impl_aux_rel rest beats ->
      parse_music_impl_aux_rel (note :: rest) (beat :: beats)
  | pmiar_skip : forall note rest beats,
      ~ (exists beat, parse_note_rel note beat) ->
      parse_music_impl_aux_rel rest beats ->
      parse_music_impl_aux_rel (note :: rest) beats.



Definition parse_music_Spec (input : list ascii) (output : list nat) : Prop :=
  exists groups,
    SplitOnSpaces_rel input groups /\
    parse_music_impl_aux_rel groups output.
