
Require Import Coq.Strings.String.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetWeakList.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FSetFacts.

Module String_as_OT := 
  struct
    Definition t := string.
    Definition eq := @eq string.
    Definition lt := String.lt.
    Definition eq_refl := @eq_refl string.
    Definition eq_sym := @eq_sym string.
    Definition eq_trans := @eq_trans string.
    Definition lt_trans := String.lt_trans.
    Definition lt_not_eq := String.lt_not_eq.
    Definition compare := String.compare.
    Definition compare_eq_iff := String.compare_eq_iff.
  End.

Module StrSet := FSetAVL.Make(String_as_OT).
Module StrSetFacts := FSetFacts.WFacts(StrSet).

Definition chars_in (s : string) : StrSet.t :=
  let fix chars_aux i :=
      match i with
      | O => StrSet.empty
      | S i' => StrSet.add (String.get (S i') s) (chars_aux i')
      end
  in chars_aux (String.length s).

Definition same_chars_spec (s0 s1 : string) : Prop :=
  chars_in s0 = chars_in s1.

