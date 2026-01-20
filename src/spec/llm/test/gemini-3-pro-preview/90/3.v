Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition next_smallest_spec (lst : list Z) (res : option Z) : Prop :=
  match res with
  | None => 
      forall x y, In x lst -> In y lst -> x = y
  | Some z => 
      In z lst /\
      exists m, 
        In m lst /\ 
        (forall k, In k lst -> m <= k) /\ 
        m < z /\ 
        (forall x, In x lst -> m < x -> z <= x)
  end.

Example test_case : next_smallest_spec [] None.
Proof.
  unfold next_smallest_spec.
  intros x y Hx Hy.
  inversion Hx.
Qed.