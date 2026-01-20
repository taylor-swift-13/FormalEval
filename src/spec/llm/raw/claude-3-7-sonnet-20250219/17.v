
Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Definition count_beats_spec (note : string) (beats : nat) : Prop :=
  (note = "o" /\ beats = 4) \/
  (note = "o|" /\ beats = 2) \/
  (note = ".|" /\ beats = 1).

Fixpoint map_spec {A B : Type} (f : A -> B -> Prop) (l : list A) (res : list B) : Prop :=
  match l, res with
  | [], [] => True
  | x :: xs, y :: ys => f x y /\ map_spec f xs ys
  | _, _ => False
  end.

Definition parse_music_spec (music_string : string) (beats_list : list nat) : Prop :=
  (music_string = "" /\ beats_list = []) \/
  (exists notes,
     String.split " " music_string = notes /\
     map_spec count_beats_spec notes beats_list).
