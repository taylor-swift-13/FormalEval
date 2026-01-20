Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

Local Open Scope string_scope.

Fixpoint count_char (s : string) (c : ascii) : nat :=
  match s with
  | EmptyString => 0
  | String a s' =>
      match Ascii.ascii_dec a c with
      | left _ => S (count_char s' c)
      | right _ => count_char s' c
      end
  end.

Definition balanced (s : string) : Prop :=
  count_char s "(")%char = count_char s ")"%char /\
  forall t u, s = String.append t u ->
    le (count_char t ")"%char) (count_char t "(")%char.

Fixpoint only_parens (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String a s' => ((a = "(")%char \/ a = ")"%char) /\ only_parens s'
  end.

Definition match_parens_spec (lst : list string) (res : string) : Prop :=
  exists s0 s1,
    lst = s0 :: s1 :: nil /\
    only_parens s0 /\ only_parens s1 /\
    ((res = "Yes" /\ (balanced (String.append s0 s1) \/ balanced (String.append s1 s0)))
     \/ (res = "No" /\ ~(balanced (String.append s0 s1) \/ balanced (String.append s1 s0)))).