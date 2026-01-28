Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
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

Fixpoint starts_with (p s : string) : bool :=
  match p with
  | EmptyString => true
  | String c p' =>
    match s with
    | EmptyString => false
    | String c' s' => if Ascii.eqb c c' then starts_with p' s' else false
    end
  end.

Fixpoint contains_bool (sub s : string) : bool :=
  if starts_with sub s then true
  else match s with
       | EmptyString => false
       | String _ s' => contains_bool sub s'
       end.

Lemma contains_bool_true : forall sub s, contains_bool sub s = true -> contains_substring sub s.
Proof. Admitted.

Lemma contains_bool_false : forall sub s, contains_bool sub s = false -> ~ contains_substring sub s.
Proof. Admitted.

Example test_case : filter_by_substring_spec [
  "We the people of the United States of America, in order to form a more perfect union, establish justice, insure domestic tranquility, provide for the common defense, promote the general welfare, and secure the blessings of liberty to ourselves and our posterity, do ordain and establish this Constitution for the United States of America.";
  "To be or not to be, that is the question.";
  "It is a truth universally acknowledged, that a single man in possession of a good fortune, must be in want of a wife.";
  "I have a dream that one day this nation will rise up and live out the true meaning of its creed: ""We hold these truths to be self-evident, that all men are created equal.""";
  "Four score and seven years ago our fathers brought forth on this continent, a new nation, conceived in Liberty, and dedicated to the proposition that all men are created equal."
  ] "equal." [
  "I have a dream that one day this nation will rise up and live out the true meaning of its creed: ""We hold these truths to be self-evident, that all men are created equal.""";
  "Four score and seven years ago our fathers brought forth on this continent, a new nation, conceived in Liberty, and dedicated to the proposition that all men are created equal."
  ].
Proof.
  unfold filter_by_substring_spec.
  apply filtered_cons_false.
  { apply contains_bool_false. reflexivity. }
  apply filtered_cons_false.
  { apply contains_bool_false. reflexivity. }
  apply filtered_cons_false.
  { apply contains_bool_false. reflexivity. }
  apply filtered_cons_true.
  { apply contains_bool_true. reflexivity. }
  apply filtered_cons_true.
  { apply contains_bool_true. reflexivity. }
  apply filtered_nil.
Qed.