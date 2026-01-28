Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition contains_substring (substring s : string) : Prop :=
  exists pre post, s = String.append pre (String.append substring post).

Inductive filtered (P : string -> Prop) : list string -> list string -> Prop :=
| filtered_nil : filtered P [] []
| filtered_cons_true : forall x l l', P x -> filtered P l l' -> filtered P (x :: l) (x :: l')
| filtered_cons_false : forall x l l', ~ P x -> filtered P l l' -> filtered P (x :: l) l'.

Definition filter_by_substring_spec (strings : list string) (substring : string) (res : list string) : Prop :=
  filtered (contains_substring substring) strings res.

Example test_case : filter_by_substring_spec ["moon"; "stars"; "sun"; "planets"] "s" ["stars"; "sun"; "planets"].
Proof.
  unfold filter_by_substring_spec.
  apply filtered_cons_false.
  - unfold contains_substring. intros [pre [post H]].
    destruct pre; simpl in H; try discriminate.
    destruct pre; simpl in H; try discriminate.
    destruct pre; simpl in H; try discriminate.
    destruct pre; simpl in H; try discriminate.
    destruct pre; simpl in H; try discriminate.
  - apply filtered_cons_true.
    + exists "", "tars". reflexivity.
    + apply filtered_cons_true.
      * exists "", "un". reflexivity.
      * apply filtered_cons_true.
        { exists "planet", "". reflexivity. }
        { apply filtered_nil. }
Qed.