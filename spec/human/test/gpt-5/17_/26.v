Require Import Ascii String List ZArith.
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

Inductive parse_note_rel : string -> Z -> Prop :=
  | pnr_whole : parse_note_rel "o" 4%Z
  | pnr_half : parse_note_rel "o|" 2%Z
  | pnr_quarter : parse_note_rel ".|" 1%Z.

Inductive parse_music_impl_aux_rel : list string -> list Z -> Prop :=
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

Definition problem_17_spec (input : string) (output : list Z) : Prop :=
  exists groups,
    SplitOnSpaces_rel input groups /\
    parse_music_impl_aux_rel groups output.

Example test_case_empty_input : problem_17_spec "o| o| o| .|" [2%Z; 2%Z; 2%Z; 1%Z].
Proof.
  unfold problem_17_spec.
  exists ["o|"; "o|"; "o|"; ".|"].
  split.
  - apply sos_base.
    eapply sosar_char.
    + discriminate.
    + eapply sosar_char.
      * discriminate.
      * eapply sosar_space_nonempty.
        -- reflexivity.
        -- simpl. discriminate.
        -- eapply sosar_char.
           ++ discriminate.
           ++ eapply sosar_char.
              ** discriminate.
              ** eapply sosar_space_nonempty.
                 --- reflexivity.
                 --- simpl. discriminate.
                 --- eapply sosar_char.
                     +++ discriminate.
                     +++ eapply sosar_char.
                         **** discriminate.
                         **** eapply sosar_space_nonempty.
                              ----- reflexivity.
                              ----- simpl. discriminate.
                              ----- eapply sosar_char.
                                    +++++ discriminate.
                                    +++++ eapply sosar_char.
                                          ****** discriminate.
                                          ****** apply sosar_nil_nonempty.
                                                 simpl. discriminate.
  - eapply pmiar_cons.
    + apply pnr_half.
    + eapply pmiar_cons.
      * apply pnr_half.
      * eapply pmiar_cons.
        -- apply pnr_half.
        -- eapply pmiar_cons.
           ++ apply pnr_quarter.
           ++ apply pmiar_nil.
Qed.