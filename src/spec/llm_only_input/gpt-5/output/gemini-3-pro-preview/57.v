Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Inductive sorted_inc : list Z -> Prop :=
  | sorted_inc_nil : sorted_inc []
  | sorted_inc_one : forall x, sorted_inc [x]
  | sorted_inc_cons : forall x y l, x <= y -> sorted_inc (y :: l) -> sorted_inc (x :: y :: l).

Inductive sorted_dec : list Z -> Prop :=
  | sorted_dec_nil : sorted_dec []
  | sorted_dec_one : forall x, sorted_dec [x]
  | sorted_dec_cons : forall x y l, x >= y -> sorted_dec (y :: l) -> sorted_dec (x :: y :: l).

Definition monotonic_spec (l : list Z) (res : bool) : Prop :=
  res = true <-> (sorted_inc l \/ sorted_dec l).

Example monotonic_spec_test :
  monotonic_spec [1%Z; 2%Z; 4%Z; 10%Z] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _. left.
    apply sorted_inc_cons with (x:=1%Z) (y:=2%Z) (l:=[4%Z; 10%Z]).
    + lia.
    + apply sorted_inc_cons with (x:=2%Z) (y:=4%Z) (l:=[10%Z]).
      * lia.
      * apply sorted_inc_cons with (x:=4%Z) (y:=10%Z) (l:=[]).
        { lia. }
        { apply sorted_inc_one. }
  - intros _. reflexivity.
Qed.