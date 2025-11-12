
Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.OptionDef.

Definition string_to_md5_spec (text : string) (result : option string) : Prop :=
  (text = "" /\ result = None) \/
  (text <> "" /\ result = Some (* the md5 hash string of text *)).
