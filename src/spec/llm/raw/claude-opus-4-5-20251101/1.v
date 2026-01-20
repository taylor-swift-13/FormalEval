
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Fixpoint count_char (s : string) (c : ascii) : Z :=
  match s with
  | EmptyString => 0
  | String h t => if Ascii.eqb h c then 1 + count_char t c else count_char t c
  end.

Definition is_balanced (s : string) : Prop :=
  count_char s "("%char = count_char s ")"%char.

Fixpoint remove_spaces (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String h t => if Ascii.eqb h " "%char then remove_spaces t else String h (remove_spaces t)
  end.

Fixpoint all_prefixes_nonneg (s : string) (cnt : Z) : Prop :=
  match s with
  | EmptyString => True
  | String h t =>
    let new_cnt := if Ascii.eqb h "("%char then cnt + 1
                   else if Ascii.eqb h ")"%char then cnt - 1
                   else cnt in
    new_cnt >= 0 /\ all_prefixes_nonneg t new_cnt
  end.

Definition is_valid_group (s : string) : Prop :=
  s <> EmptyString /\
  is_balanced s /\
  all_prefixes_nonneg s 0 /\
  (forall i, 0 < i < Z.of_nat (String.length s) -> 
    exists prefix, String.length prefix = Z.to_nat i /\
    count_char prefix "("%char > count_char prefix ")"%char).

Fixpoint concat_strings (l : list string) : string :=
  match l with
  | [] => EmptyString
  | h :: t => append h (concat_strings t)
  end.

Definition separate_paren_groups_spec (paren_string : string) (result : list string) : Prop :=
  let cleaned := remove_spaces paren_string in
  concat_strings result = cleaned /\
  Forall is_valid_group result /\
  (forall g1 g2, In g1 result -> In g2 result -> g1 <> g2 -> 
    True).
