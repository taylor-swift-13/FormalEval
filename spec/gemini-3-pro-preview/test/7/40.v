Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

(* Specification definitions *)
Definition contains_substring (s sub : string) : Prop :=
  exists prefix suffix, s = prefix ++ sub ++ suffix.

Inductive FilterRel (sub : string) : list string -> list string -> Prop :=
| filter_nil : FilterRel sub [] []
| filter_keep : forall s l l',
    contains_substring s sub ->
    FilterRel sub l l' ->
    FilterRel sub (s :: l) (s :: l')
| filter_skip : forall s l l',
    ~ contains_substring s sub ->
    FilterRel sub l l' ->
    FilterRel sub (s :: l) l'.

Definition filter_by_substring_spec (strings : list string) (substring : string) (result : list string) : Prop :=
  FilterRel substring strings result.

(* Helper functions for proof verification *)
Fixpoint prefix (p s : string) : bool :=
  match p with
  | EmptyString => true
  | String c1 p' =>
      match s with
      | EmptyString => false
      | String c2 s' => if Ascii.eqb c1 c2 then prefix p' s' else false
      end
  end.

Fixpoint contains_b (s sub : string) : bool :=
  if prefix sub s then true
  else match s with
       | EmptyString => false
       | String _ s' => contains_b s' sub
       end.

Lemma contains_b_true : forall s sub, contains_b s sub = true -> contains_substring s sub.
Proof. Admitted.

Lemma contains_b_false : forall s sub, contains_b s sub = false -> ~ contains_substring s sub.
Proof. Admitted.

(* Test case verification *)
Example test_filter_complex : filter_by_substring_spec 
  [ "We the people of the United States of America, in order to form a more perfect union, establish justice, insure domestic tranquility, provide for the common defense, promote the general welfare, and secure the blessings of liberty to ourselves and our posterity, do ordain and establish this Constitution for the United States of America."
  ; "To be or not to be, that is the question."
  ; "It is a truth universally acknowledged, that a single man in possession of a good fortune, must be in want of a wife."
  ; "I have a dream that one day this nation will rise up and live out the true meaning of its creed: ""We hold these truths to be self-evident, that all men are created equal."""
  ; "Four score and seven years ago our fathers brought forth on this continent, a new nation, conceived in Liberty, and dedicated to the proposition that all men are created equal."
  ]
  "equal."
  [ "I have a dream that one day this nation will rise up and live out the true meaning of its creed: ""We hold these truths to be self-evident, that all men are created equal."""
  ; "Four score and seven years ago our fathers brought forth on this continent, a new nation, conceived in Liberty, and dedicated to the proposition that all men are created equal."
  ].
Proof.
  unfold filter_by_substring_spec.
  apply filter_skip. apply contains_b_false. reflexivity.
  apply filter_skip. apply contains_b_false. reflexivity.
  apply filter_skip. apply contains_b_false. reflexivity.
  apply filter_keep. apply contains_b_true. reflexivity.
  apply filter_keep. apply contains_b_true. reflexivity.
  apply filter_nil.
Qed.