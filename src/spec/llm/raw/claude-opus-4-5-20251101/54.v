 
Require Import Coq.Strings.String.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Import ListNotations.

Definition char_set (s : string) : Ensemble ascii :=
  fun c => exists i, get i s = Some c.

Definition same_chars_spec (s0 : string) (s1 : string) (result : bool) : Prop :=
  result = true <-> (forall c : ascii, char_set s0 c <-> char_set s1 c).
