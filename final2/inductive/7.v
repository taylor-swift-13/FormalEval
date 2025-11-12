(*  Filter an input list of strings only for ones that contain given substring
>>> filter_by_substring([], 'a')
[]
>>> filter_by_substring(['abc', 'bacd', 'cde', 'array'], 'a')
['abc', 'bacd', 'array']
 *)

Require Import List.
Require Import String.
Import ListNotations.

Open Scope string_scope.

Inductive contains_substring_rel : string -> string -> Prop :=
  | csr_empty : forall sub, sub = EmptyString -> contains_substring_rel EmptyString sub
  | csr_prefix : forall s sub, String.prefix s sub = true -> contains_substring_rel s sub
  | csr_cons : forall c rest sub,
      contains_substring_rel rest sub ->
      contains_substring_rel (String c rest) sub.

Inductive filter_by_substring_impl_rel : list string -> string -> list string -> Prop :=
  | fbsir_nil : forall sub, filter_by_substring_impl_rel [] sub []
  | fbsir_include : forall h t sub output,
      contains_substring_rel h sub ->
      filter_by_substring_impl_rel t sub output ->
      filter_by_substring_impl_rel (h :: t) sub (h :: output)
  | fbsir_exclude : forall h t sub output,
      ~ contains_substring_rel h sub ->
      filter_by_substring_impl_rel t sub output ->
      filter_by_substring_impl_rel (h :: t) sub output.

Definition spec_filter_by_substring (input output : list string) (sub : string) : Prop :=
  filter_by_substring_impl_rel input sub output.
