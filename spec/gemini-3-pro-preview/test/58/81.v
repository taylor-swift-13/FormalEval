Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope string_scope.

Definition common_spec (l1 : list string) (l2 : list Z) (res : list Z) : Prop :=
  Sorted Z.le res /\
  NoDup res /\
  (forall x : Z, In x res <-> (False /\ In x l2)).

Example test_common_spec :
  common_spec 
    ["SgmW"; "wdIIZAXJqx"; "sRbO"; "mqbFo"; ""; "vZmyAs"; "dajGeqFZ"; "Jr"; "Hv"]
    [1%Z; 2%Z; 3%Z; 1%Z; 2%Z] 
    [].
Proof.
  unfold common_spec.
  split.
  - (* Sorted *)
    constructor.
  - split.
    + (* NoDup *)
      constructor.
    + (* Equivalence *)
      intros x. split.
      * intro H. inversion H.
      * intros [H _]. contradiction.
Qed.