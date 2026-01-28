Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* Specification definitions *)
Definition contains_substring (s sub : string) : Prop :=
  exists prefix suffix, s = prefix ++ sub ++ suffix.

Inductive FilterRel (sub : string) : list string -> list string -> Prop :=
| filter_nil : FilterRel sub [] []
| filter_keep : forall s l l',
    contains_substring s sub ->
    FilterRel sub l l' ->
    FilterRel sub (s :: l) (s :: l')
| filter_skip : forall s l l',
    ~ contains_substring s sub ->
    FilterRel sub l l' ->
    FilterRel sub (s :: l) l'.

Definition filter_by_substring_spec (strings : list string) (substring : string) (result : list string) : Prop :=
  FilterRel substring strings result.

(* Test case verification *)
(* Input: strings = ["banana"; "apple"; "kiwi"; "peach"], substring = "a" *)
(* Output: result = ["banana"; "apple"; "peach"] *)

Example test_filter_fruits : filter_by_substring_spec ["banana"; "apple"; "kiwi"; "peach"] "a" ["banana"; "apple"; "peach"].
Proof.
  unfold filter_by_substring_spec.
  (* banana *)
  apply filter_keep.
  { exists "b", "nana". reflexivity. }
  (* apple *)
  apply filter_keep.
  { exists "", "pple". reflexivity. }
  (* kiwi *)
  apply filter_skip.
  {
    unfold contains_substring. intros [p [s H]].
    destruct p.
    - simpl in H. discriminate.
    - simpl in H. injection H as H1 H2. subst.
      destruct p.
      + simpl in H2. discriminate.
      + simpl in H2. injection H2 as H3 H4. subst.
        destruct p.
        * simpl in H4. discriminate.
        * simpl in H4. injection H4 as H5 H6. subst.
          destruct p.
          { simpl in H6. discriminate. }
          { simpl in H6. injection H6 as H7 H8. subst.
            destruct p; simpl in H8; discriminate. }
  }
  (* peach *)
  apply filter_keep.
  { exists "pe", "ch". reflexivity. }
  (* nil *)
  apply filter_nil.
Qed.