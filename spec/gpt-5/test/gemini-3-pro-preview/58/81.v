Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Definition common_spec (l1 : list string) (l2 : list Z) (out : list Z) : Prop :=
  out = [].

Example test_common_spec : 
  common_spec 
    ["SgmW"; "wdIIZAXJqx"; "sRbO"; "mqbFo"; ""; "vZmyAs"; "dajGeqFZ"; "Jr"; "Hv"] 
    [1; 2; 3; 1; 2] 
    [].
Proof.
  unfold common_spec.
  reflexivity.
Qed.