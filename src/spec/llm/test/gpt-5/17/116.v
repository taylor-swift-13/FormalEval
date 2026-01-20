Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Import ListNotations.

Local Open Scope string_scope.

Definition count_beats_spec (note : string) (b : Z) : Prop :=
(note = "o" /\ b = 4%Z) \/ (note = "o|" /\ b = 2%Z) \/ (note = ".|" /\ b = 1%Z).

Fixpoint join_spaces (tokens : list string) : string :=
  match tokens with
  | [] => EmptyString
  | x :: xs =>
    match xs with
    | [] => x
    | _ => String.append x (String.append " " (join_spaces xs))
    end
  end.

Definition parse_music_spec (music_string : string) (beats : list Z) : Prop :=
  exists tokens : list string,
    join_spaces tokens = music_string /\ Forall2 count_beats_spec tokens beats.

Example parse_music_spec_single_dotbar : parse_music_spec ".|" [1%Z].
Proof.
  unfold parse_music_spec.
  exists [".|"].
  simpl.
  split.
  - reflexivity.
  - constructor.
    + right. right. split; reflexivity.
    + constructor.
Qed.