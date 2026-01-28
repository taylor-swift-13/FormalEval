Require Import Ascii String List.
Import ListNotations.
Open Scope string_scope.

Inductive SplitOnSpaces_aux_rel : string -> string -> list string -> Prop :=
  | sosar_nil_empty : forall current_group, current_group = "" -> SplitOnSpaces_aux_rel current_group "" []
  | sosar_nil_nonempty : forall current_group, current_group <> "" -> SplitOnSpaces_aux_rel current_group "" [current_group]
  | sosar_space_empty : forall current_group h t result,
      h = " "%char ->
      current_group = "" ->
      SplitOnSpaces_aux_rel "" t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result
  | sosar_space_nonempty : forall current_group h t result,
      h = " "%char ->
      current_group <> "" ->
      SplitOnSpaces_aux_rel "" t result ->
      SplitOnSpaces_aux_rel current_group (String h t) (current_group :: result)
  | sosar_char : forall current_group h t result,
      h <> " "%char ->
      SplitOnSpaces_aux_rel (current_group ++ String h "") t result ->
      SplitOnSpaces_aux_rel current_group (String h t) result.

Inductive SplitOnSpaces_rel : string -> list string -> Prop :=
  | sos_base : forall S result, SplitOnSpaces_aux_rel "" S result -> SplitOnSpaces_rel S result.

Inductive parse_note_rel : string -> nat -> Prop :=
  | pnr_whole : parse_note_rel "o" 4
  | pnr_half : parse_note_rel "o|" 2
  | pnr_quarter : parse_note_rel ".|" 1.

Inductive parse_music_impl_aux_rel : list string -> list nat -> Prop :=
  | pmiar_nil : parse_music_impl_aux_rel [] []
  | pmiar_cons : forall note rest beats beat,
      parse_note_rel note beat ->
      parse_music_impl_aux_rel rest beats ->
      parse_music_impl_aux_rel (note :: rest) (beat :: beats)
  | pmiar_skip : forall note rest beats,
      ~ (exists beat, parse_note_rel note beat) ->
      parse_music_impl_aux_rel rest beats ->
      parse_music_impl_aux_rel (note :: rest) beats.

Definition problem_17_pre (input : string) : Prop := True.

Definition problem_17_spec (input : string) (output : list nat) : Prop :=
  exists groups,
    SplitOnSpaces_rel input groups /\
    parse_music_impl_aux_rel groups output.

Example test_o_o_pipe_o : problem_17_spec "o o| o" [4; 2; 4].
Proof.
  unfold problem_17_spec.
  exists ["o"; "o|"; "o"].
  split.
  - apply sos_base.
    apply sosar_char.
    + discriminate.
    + simpl.
      apply sosar_space_nonempty.
      * reflexivity.
      * discriminate.
      * apply sosar_char.
        -- discriminate.
        -- simpl.
           apply sosar_char.
           ++ discriminate.
           ++ simpl.
              apply sosar_space_nonempty.
              ** reflexivity.
              ** discriminate.
              ** apply sosar_char.
                 --- discriminate.
                 --- simpl.
                     apply sosar_nil_nonempty.
                     discriminate.
  - apply pmiar_cons with (beat := 4).
    + apply pnr_whole.
    + apply pmiar_cons with (beat := 2).
      * apply pnr_half.
      * apply pmiar_cons with (beat := 4).
        -- apply pnr_whole.
        -- apply pmiar_nil.
Qed.