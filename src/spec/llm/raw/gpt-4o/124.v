
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

Definition valid_date_spec (date : string) (is_valid : bool) : Prop :=
  let days := [31; 29; 31; 30; 31; 30; 31; 31; 30; 31; 30; 31] in
  (String.length date =? 10) = true /\
  (String.get 2 date = Some "-") /\
  (String.get 5 date = Some "-") /\
  (forall m d y,
      String.substring 0 2 date = Some m /\
      String.substring 3 2 date = Some d /\
      String.substring 6 4 date = Some y ->
      (forall mn dn yn,
          (m = string_of_nat mn /\ d = string_of_nat dn /\ y = string_of_nat yn) ->
          (1 <= mn <= 12)%nat /\
          (1 <= dn <= nth (mn - 1) days 0)%nat)) ->
  is_valid = true.
