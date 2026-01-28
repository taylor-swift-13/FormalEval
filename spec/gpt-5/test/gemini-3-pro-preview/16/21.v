Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Import ListNotations.

Definition ascii_lower (a : ascii) : ascii :=
  let n := nat_of_ascii a in
  if (65 <=? n) && (n <=? 90) then ascii_of_nat (n + 32) else a.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String a t => a :: list_of_string t
  end.

Definition count_distinct_characters_spec (s : string) (n : nat) : Prop :=
  let L := map ascii_lower (list_of_string s) in
  exists U : list ascii,
    NoDup U /\ (forall x, In x U <-> In x L) /\ length U = n.

Example test_count_distinct_complex : 
  count_distinct_characters_spec "AaBbCcThe quick brown fox jumps over the lazy doAbCdEfGgDdEeFfhello worldGgHhIi" 27.
Proof.
  unfold count_distinct_characters_spec.
  eexists (nodup ascii_dec (map ascii_lower (list_of_string "AaBbCcThe quick brown fox jumps over the lazy doAbCdEfGgDdEeFfhello worldGgHhIi"))).
  split.
  - apply NoDup_nodup.
  - split.
    + intros x. apply nodup_In.
    + vm_compute. reflexivity.
Qed.