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

Ltac build_string_step :=
  match goal with
  | |- SplitOnSpaces_aux_rel "" (String " " ?t) _ =>
    eapply sosar_space_empty; [reflexivity | reflexivity | ]
  | |- SplitOnSpaces_aux_rel ?g (String " " ?t) _ =>
    eapply sosar_space_nonempty; [reflexivity | discriminate | ]
  | |- SplitOnSpaces_aux_rel ?g (String ?h ?t) _ =>
    eapply sosar_char; [discriminate | simpl]
  | |- SplitOnSpaces_aux_rel "" "" [] =>
    apply sosar_nil_empty; reflexivity
  | |- SplitOnSpaces_aux_rel ?g "" [?g] =>
    apply sosar_nil_nonempty; discriminate
  end.

Ltac build_split := repeat build_string_step.

Ltac build_music_step :=
  match goal with
  | |- parse_music_impl_aux_rel [] [] => apply pmiar_nil
  | |- parse_music_impl_aux_rel (".|" :: _) (_ :: _) =>
    apply pmiar_cons; [apply pnr_quarter | ]
  | |- parse_music_impl_aux_rel ("o|" :: _) (_ :: _) =>
    apply pmiar_cons; [apply pnr_half | ]
  | |- parse_music_impl_aux_rel ("o" :: _) (_ :: _) =>
    apply pmiar_cons; [apply pnr_whole | ]
  end.

Ltac build_music := repeat build_music_step.

Example test_music : problem_17_spec ".| .| o| o| .| .| o| o o| o| .| .| o| o| o| o| o| .| o| o| o| o| o| o o o o o o o| o| o| o| o| .| o| o|" [1; 1; 2; 2; 1; 1; 2; 4; 2; 2; 1; 1; 2; 2; 2; 2; 2; 1; 2; 2; 2; 2; 2; 4; 4; 4; 4; 4; 4; 2; 2; 2; 2; 2; 1; 2; 2].
Proof.
  unfold problem_17_spec.
  exists [".|"; ".|"; "o|"; "o|"; ".|"; ".|"; "o|"; "o"; "o|"; "o|"; ".|"; ".|"; "o|"; "o|"; "o|"; "o|"; "o|"; ".|"; "o|"; "o|"; "o|"; "o|"; "o|"; "o"; "o"; "o"; "o"; "o"; "o"; "o|"; "o|"; "o|"; "o|"; "o|"; ".|"; "o|"; "o|"].
  split.
  - apply sos_base.
    build_split.
  - build_music.
Qed.