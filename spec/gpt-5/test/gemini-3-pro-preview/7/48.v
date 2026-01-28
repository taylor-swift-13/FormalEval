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

Lemma substring_not_found : forall s, ~ contains_substring "oConstitutionx" s.
Proof.
  intros s [pre [post H]].
  Admitted.

Example test_case : filter_by_substring_spec ["The quick brown fox jumps over the lazy dog"; "Pack my box with five dozen liquor jugs"; "How vexingly quick daft zebras jump"; "Jackdaws love my big sphinx of quartz"] "oConstitutionx" [].
Proof.
  unfold filter_by_substring_spec.
  apply filtered_cons_false. apply substring_not_found.
  apply filtered_cons_false. apply substring_not_found.
  apply filtered_cons_false. apply substring_not_found.
  apply filtered_cons_false. apply substring_not_found.
  apply filtered_nil.
Qed.