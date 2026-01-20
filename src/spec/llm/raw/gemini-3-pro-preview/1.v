
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.
Open Scope Z_scope.

Fixpoint separate_aux (s : string) (cnt : Z) (group : string) (results : list string) : list string :=
  match s with
  | EmptyString => results
  | String ch rest =>
      let cnt1 := if Ascii.eqb ch "(" then cnt + 1 else cnt in
      let cnt2 := if Ascii.eqb ch ")" then cnt1 - 1 else cnt1 in
      let group' := if Ascii.eqb ch " " then group else (group ++ String ch EmptyString)%string in
      if Z.eqb cnt2 0 then
        let results' := if string_dec group' EmptyString then results else results ++ [group'] in
        separate_aux rest 0 EmptyString results'
      else
        separate_aux rest cnt2 group' results
  end.

Definition separate_paren_groups_spec (paren_string : string) (result : list string) : Prop :=
  result = separate_aux paren_string 0 EmptyString [].
