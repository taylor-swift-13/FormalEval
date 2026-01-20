Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition how_many_times_spec (s : string) (sub : string) (res : nat) : Prop :=
  res = List.length (List.filter (fun i => String.eqb (substring i (String.length sub) s) sub) (seq 0 (String.length s))).

Example test_case_long_strings_match: how_many_times_spec "faaaaaaaabaaaaoaaabbThe quicfoxamlazyet,k brownfoipsuconsequickcfoxquicfoxcaccccccackurmx fox jumups over the lazy dog.aabbbbaaaaiconsecteturmx" "faaaaaaaabaaaaoaaabbThe quicfoxamlazyet,k brownfoipsuconsequickcfoxquicfoxcaccccccackurmx fox jumups over the lazy dog.aabbbbaaaaiconsecteturmx" 1.
Proof.
  unfold how_many_times_spec.
  vm_compute.
  reflexivity.
Qed.