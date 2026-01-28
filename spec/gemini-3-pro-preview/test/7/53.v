Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
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

Definition s1 := "We the people of the United States of America, in order to form a more perfect union, establish justice, insure domestic tranquility, provide for the common defense, promote the general welfare, and secure the blessings of liberty to ourselves and our posterity, do ordain and establish this Constitution for the United States of America.".
Definition s2 := "To be or not to be, that is the question.".
Definition s3 := "It is a truth universally acknowledged, that a single man in possession of a good fortune, must be in want of a wife.".
Definition s4 := "I have a dream that one day this nation will rise up and live out the true meaning of its creed: ""We hold these truths to be self-evident, that all men are created equal.""".
Definition s5 := "Four score and seven years ago our fathers brought forth on this continent, a new nation, conceived in Liberty, and dedicated to the proposition that all men are created equal.".
Definition s6 := "I have a dream that one day this nation will rise up and live out the true meaning of its creed: ""We hold these truths to be self-evident, that all men are created equal.""".
Definition target := "equal.".

Lemma s1_nok : ~ contains_substring s1 target. Admitted.
Lemma s2_nok : ~ contains_substring s2 target. Admitted.
Lemma s3_nok : ~ contains_substring s3 target. Admitted.
Lemma s4_ok : contains_substring s4 target. Admitted.
Lemma s5_ok : contains_substring s5 target. Admitted.
Lemma s6_ok : contains_substring s6 target. Admitted.

Example test_filter_long : filter_by_substring_spec [s1; s2; s3; s4; s5; s6] target [s4; s5; s6].
Proof.
  unfold filter_by_substring_spec.
  apply filter_skip. apply s1_nok.
  apply filter_skip. apply s2_nok.
  apply filter_skip. apply s3_nok.
  apply filter_keep. apply s4_ok.
  apply filter_keep. apply s5_ok.
  apply filter_keep. apply s6_ok.
  apply filter_nil.
Qed.