Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module StringMap := FMapList.Make(String_as_OT).

Definition string_map := StringMap.t Z.

(* Helper function to split a string by a separator *)
Fixpoint split_string_aux (s : string) (sep : string) (acc : string) : list string :=
  match s with
  | EmptyString => if (string_dec acc EmptyString) then [] else [acc]
  | String c s' =>
      let cs := String c EmptyString in
      if (string_dec cs sep) then
        if (string_dec acc EmptyString) then
          split_string_aux s' sep EmptyString
        else
          acc :: split_string_aux s' sep EmptyString
      else
        split_string_aux s' sep (acc ++ cs)
  end.

Definition split_string (s : string) (sep : string) : list string :=
  split_string_aux s sep EmptyString.

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
    let words := List.filter (fun w => negb (String.eqb w EmptyString)) (split_string test " ") in
    let count := count_occurrences words in
    let mx := max_count count in
    let expected := filter_max count mx in
    maps_equal result expected /\
    (forall k v, StringMap.find k result = Some v -> v = mx) /\
    (forall k v, StringMap.find k count = Some v -> v = mx -> StringMap.find k result = Some v)).

Example test_histogram : 
  let input := "a b b a" in
  let output := StringMap.add "a" 2 (StringMap.add "b" 2 (StringMap.empty Z)) in
  histogram_spec input output.
Proof.
  unfold histogram_spec.
  split.
  - (* Case: test = EmptyString *)
    intros H. discriminate H.
  - (* Case: test <> EmptyString *)
    intros _.
    repeat split.
    + (* maps_equal result expected *)
      unfold maps_equal. intros k.
      (* Simplify the computation for the concrete input *)
      vm_compute.
      (* Destruct based on the comparison of k with the keys "a" and "b" *)
      (* The map is sorted, so "a" is checked first, then "b" *)
      destruct (String.compare "a" k) eqn:Ca.
      * reflexivity. (* k = "a" *)
      * reflexivity. (* k < "a", both None *)
      * destruct (String.compare "b" k) eqn:Cb.
        -- reflexivity. (* k = "b" *)
        -- reflexivity. (* "a" < k < "b", both None *)
        -- reflexivity. (* k > "b", both None *)

    + (* forall k v, StringMap.find k result = Some v -> v = mx *)
      intros k v Hfind.
      vm_compute in Hfind.
      (* Check keys "a" and "b" *)
      destruct (String.compare "a" k) eqn:Ca.
      * injection Hfind as Heq. exact Heq.
      * discriminate Hfind.
      * destruct (String.compare "b" k) eqn:Cb.
        -- injection Hfind as Heq. exact Heq.
        -- discriminate Hfind.
        -- discriminate Hfind.

    + (* forall k v, StringMap.find k count = Some v -> v = mx -> StringMap.find k result = Some v *)
      intros k v Hfind Hval.
      vm_compute in Hfind.
      vm_compute.
      (* Check keys "a" and "b" *)
      destruct (String.compare "a" k) eqn:Ca.
      * assumption.
      * discriminate Hfind.
      * destruct (String.compare "b" k) eqn:Cb.
        -- assumption.
        -- discriminate Hfind.
        -- discriminate Hfind.
Qed.