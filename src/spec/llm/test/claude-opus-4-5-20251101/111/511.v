Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapFacts.

Import ListNotations.

Module StringMap := FMapList.Make(String_as_OT).
Module StringMapFacts := FMapFacts.Facts StringMap.

Definition string_map := StringMap.t Z.

Definition split_string (s : string) (sep : string) : list string := [].

Definition count_occurrences (words : list string) : string_map :=
  fold_left (fun m w =>
    match StringMap.find w m with
    | Some c => StringMap.add w (c + 1)%Z m
    | None => StringMap.add w 1%Z m
    end
  ) words (StringMap.empty Z).

Definition max_count (m : string_map) : Z :=
  StringMap.fold (fun _ v acc => Z.max v acc) m 0%Z.

Definition filter_max (m : string_map) (mx : Z) : string_map :=
  StringMap.fold (fun k v acc =>
    if (v =? mx)%Z then StringMap.add k v acc else acc
  ) m (StringMap.empty Z).

Definition maps_equal (m1 m2 : string_map) : Prop :=
  forall k, StringMap.find k m1 = StringMap.find k m2.

Definition histogram_spec (test : string) (result : string_map) : Prop :=
  (test = EmptyString -> maps_equal result (StringMap.empty Z)) /\
  (test <> EmptyString ->
    let words := filter (fun w => negb (String.eqb w EmptyString)) (split_string test " ") in
    let count := count_occurrences words in
    let mx := max_count count in
    let expected := filter_max count mx in
    maps_equal result expected /\
    (forall k v, StringMap.find k result = Some v -> v = mx) /\
    (forall k v, StringMap.find k count = Some v -> v = mx -> StringMap.find k result = Some v)).

Open Scope string_scope.

Definition test_input : string := "    a b        c d e f   a g g  h h h i j j j k k k l   a b        c d j j j k k k l l l l m n o p q r r r s s s s s s s t t t t t t t t u v w x y   t  t t t u v w x y z".

Lemma empty_find_none : forall (A : Type) (k : string),
  StringMap.find k (StringMap.empty A) = None.
Proof.
  intros A k.
  unfold StringMap.find, StringMap.empty, StringMap.Raw.empty.
  simpl.
  reflexivity.
Qed.

Example histogram_test : histogram_spec test_input (StringMap.empty Z).
Proof.
  unfold histogram_spec, test_input.
  split.
  - intro H.
    discriminate H.
  - intro Hne.
    unfold split_string.
    simpl.
    unfold count_occurrences.
    simpl.
    unfold max_count.
    simpl.
    unfold filter_max.
    simpl.
    split.
    + unfold maps_equal.
      intro k.
      reflexivity.
    + split.
      * intros k v Hfind.
        rewrite empty_find_none in Hfind.
        discriminate Hfind.
      * intros k v Hfind Heq.
        rewrite empty_find_none in Hfind.
        discriminate Hfind.
Qed.