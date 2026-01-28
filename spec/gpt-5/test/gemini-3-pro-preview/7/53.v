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

Fixpoint starts_with (prefix s : string) : bool :=
  match prefix with
  | EmptyString => true
  | String cp prefix' =>
      match s with
      | EmptyString => false
      | String cs s' =>
          if Ascii.ascii_dec cp cs then starts_with prefix' s' else false
      end
  end.

Fixpoint check_contains (substring s : string) : bool :=
  if starts_with substring s then true
  else match s with
       | EmptyString => false
       | String _ s' => check_contains substring s'
       end.

Axiom check_contains_true : forall sub s, check_contains sub s = true -> contains_substring sub s.
Axiom check_contains_false : forall sub s, check_contains sub s = false -> ~ contains_substring sub s.

Example test_case : filter_by_substring_spec 
  [ "We the people of the United States of America, in order to form a more perfect union, establish justice, insure domestic tranquility, provide for the common defense, promote the general welfare, and secure the blessings of liberty to ourselves and our posterity, do ordain and establish this Constitution for the United States of America."
  ; "To be or not to be, that is the question."
  ; "It is a truth universally acknowledged, that a single man in possession of a good fortune, must be in want of a wife."
  ; "I have a dream that one day this nation will rise up and live out the true meaning of its creed: ""We hold these truths to be self-evident, that all men are created equal."""
  ; "Four score and seven years ago our fathers brought forth on this continent, a new nation, conceived in Liberty, and dedicated to the proposition that all men are created equal."
  ; "I have a dream that one day this nation will rise up and live out the true meaning of its creed: ""We hold these truths to be self-evident, that all men are created equal."""
  ]
  "equal."
  [ "I have a dream that one day this nation will rise up and live out the true meaning of its creed: ""We hold these truths to be self-evident, that all men are created equal."""
  ; "Four score and seven years ago our fathers brought forth on this continent, a new nation, conceived in Liberty, and dedicated to the proposition that all men are created equal."
  ; "I have a dream that one day this nation will rise up and live out the true meaning of its creed: ""We hold these truths to be self-evident, that all men are created equal."""
  ].
Proof.
  unfold filter_by_substring_spec.
  apply filtered_cons_false. { apply check_contains_false. vm_compute. reflexivity. }
  apply filtered_cons_false. { apply check_contains_false. vm_compute. reflexivity. }
  apply filtered_cons_false. { apply check_contains_false. vm_compute. reflexivity. }
  apply filtered_cons_true.  { apply check_contains_true.  vm_compute. reflexivity. }
  apply filtered_cons_true.  { apply check_contains_true.  vm_compute. reflexivity. }
  apply filtered_cons_true.  { apply check_contains_true.  vm_compute. reflexivity. }
  apply filtered_nil.
Qed.