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

Example test_case : filter_by_substring_spec 
  ["The Shawshank Redemption"; " The Godfather "; "The Dark Knight"; "  The Lord of the Rings   "; "   Star Wars"; " Inception     "; "Forrest Gump"; " Inception     "] 
  " " 
  ["The Shawshank Redemption"; " The Godfather "; "The Dark Knight"; "  The Lord of the Rings   "; "   Star Wars"; " Inception     "; "Forrest Gump"; " Inception     "].
Proof.
  unfold filter_by_substring_spec.
  apply filtered_cons_true.
  { unfold contains_substring. exists "The", "Shawshank Redemption". reflexivity. }
  apply filtered_cons_true.
  { unfold contains_substring. exists "", "The Godfather ". reflexivity. }
  apply filtered_cons_true.
  { unfold contains_substring. exists "The", "Dark Knight". reflexivity. }
  apply filtered_cons_true.
  { unfold contains_substring. exists "", " The Lord of the Rings   ". reflexivity. }
  apply filtered_cons_true.
  { unfold contains_substring. exists "", "  Star Wars". reflexivity. }
  apply filtered_cons_true.
  { unfold contains_substring. exists "", "Inception     ". reflexivity. }
  apply filtered_cons_true.
  { unfold contains_substring. exists "Forrest", "Gump". reflexivity. }
  apply filtered_cons_true.
  { unfold contains_substring. exists "", "Inception     ". reflexivity. }
  apply filtered_nil.
Qed.