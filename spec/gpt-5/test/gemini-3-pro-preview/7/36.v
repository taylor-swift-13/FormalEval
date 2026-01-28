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

Example test_case : filter_by_substring_spec ["Washington"; "DC"; "New York City"; "Boston"; "Los Angeles"; "San Francisco"; "Miami"] "an" ["San Francisco"].
Proof.
  unfold filter_by_substring_spec.
  Ltac solve_not_contains :=
    let pre := fresh "pre" in
    let post := fresh "post" in
    let H := fresh "H" in
    intros [pre [post H]];
    repeat (
      destruct pre; simpl in H;
      [ try discriminate
      | try discriminate; injection H as _ H ]
    ).
  apply filtered_cons_false. solve_not_contains.
  apply filtered_cons_false. solve_not_contains.
  apply filtered_cons_false. solve_not_contains.
  apply filtered_cons_false. solve_not_contains.
  apply filtered_cons_false. solve_not_contains.
  apply filtered_cons_true.
  exists "S", " Francisco". simpl. reflexivity.
  apply filtered_cons_false. solve_not_contains.
  apply filtered_nil.
Qed.