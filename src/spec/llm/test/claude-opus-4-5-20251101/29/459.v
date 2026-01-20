Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint starts_with (prefix s : string) : bool :=
  match prefix, s with
  | EmptyString, _ => true
  | String c1 rest1, String c2 rest2 =>
      if Ascii.eqb c1 c2 then starts_with rest1 rest2 else false
  | String _ _, EmptyString => false
  end.

Definition filter_by_prefix_spec (strings : list string) (prefix : string) (result : list string) : Prop :=
  result = filter (fun s => starts_with prefix s) strings.

Example test_filter_by_prefix :
  filter_by_prefix_spec ["123"%string; "abc"%string; "ABC"%string; "application123"%string; "ab1c"%string; "_a_bc"%string; "abcab"%string; "abc1"%string; "tea"%string; "电"%string] "aa"%string [].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.