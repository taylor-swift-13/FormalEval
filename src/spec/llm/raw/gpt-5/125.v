Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

Definition space : ascii := Ascii.ascii_of_nat 32.
Definition newline : ascii := Ascii.ascii_of_nat 10.
Definition carriage_return : ascii := Ascii.ascii_of_nat 13.
Definition tab : ascii := Ascii.ascii_of_nat 9.
Definition comma : ascii := Ascii.ascii_of_nat 44.

Definition White (a : ascii) : Prop :=
  a = space \/ a = newline \/ a = carriage_return \/ a = tab.

Definition NonWhite (a : ascii) : Prop := ~ White a.

Inductive AllWhite : string -> Prop :=
| allwhite_empty : AllWhite EmptyString
| allwhite_cons : forall a s, White a -> AllWhite s -> AllWhite (String a s).

Inductive AllNonWhite : string -> Prop :=
| allnonwhite_empty : AllNonWhite EmptyString
| allnonwhite_cons : forall a s, NonWhite a -> AllNonWhite s -> AllNonWhite (String a s).

Definition Contains (s : string) (c : ascii) : Prop :=
  exists s1 s2, s = s1 ++ String c s2.

Definition ContainsChar (s : string) (c : ascii) : Prop := Contains s c.

Definition AnyWhitespace (s : string) : Prop :=
  exists s1 s2 c, s = s1 ++ String c s2 /\ White c.

Inductive SplitWS : string -> list string -> Prop :=
| splitws_empty : SplitWS EmptyString []
| splitws_skip : forall sep rest words,
    sep <> EmptyString ->
    AllWhite sep ->
    SplitWS rest words ->
    SplitWS (sep ++ rest) words
| splitws_token_end : forall tok,
    tok <> EmptyString ->
    AllNonWhite tok ->
    SplitWS tok [tok]
| splitws_token_next : forall tok sep rest words,
    tok <> EmptyString ->
    AllNonWhite tok ->
    sep <> EmptyString ->
    AllWhite sep ->
    SplitWS rest words ->
    SplitWS (tok ++ sep ++ rest) (tok :: words).

Inductive JoinWithChar : ascii -> list string -> string -> Prop :=
| join_one : forall c w, JoinWithChar c [w] w
| join_cons : forall c w ws s' s,
    JoinWithChar c ws s' ->
    s = w ++ String c s' ->
    JoinWithChar c (w :: ws) s.

Definition NoChar (c : ascii) (w : string) : Prop :=
  ~ ContainsChar w c.

Definition Forall_NoChar (c : ascii) (ws : list string) : Prop :=
  Forall (NoChar c) ws.

Definition SplitChar (c : ascii) (s : string) (words : list string) : Prop :=
  JoinWithChar c words s /\ Forall_NoChar c words.

Definition is_lower_az (a : ascii) : bool :=
  andb (Nat.leb 97 (nat_of_ascii a)) (Nat.leb (nat_of_ascii a) 122).

Definition odd_index_lower (a : ascii) : bool :=
  andb is_lower_az
       (Nat.eqb (Nat.modulo (Nat.sub (nat_of_ascii a) (nat_of_ascii ("a"%char))) 2) 1) a.

Fixpoint count_odd_lower (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String a s' =>
      (if odd_index_lower a then 1 else 0) + count_odd_lower s'
  end.

Inductive split_words_result :=
| RList : list string -> split_words_result
| RCount : nat -> split_words_result.

Definition split_words_spec (txt : string) (res : split_words_result) : Prop :=
  (AnyWhitespace txt /\ exists words, SplitWS txt words /\ res = RList words)
  \/
  (~ AnyWhitespace txt /\ ContainsChar txt comma /\ exists words, SplitChar comma txt words /\ res = RList words)
  \/
  (~ AnyWhitespace txt /\ ~ ContainsChar txt comma /\ res = RCount (count_odd_lower txt)).