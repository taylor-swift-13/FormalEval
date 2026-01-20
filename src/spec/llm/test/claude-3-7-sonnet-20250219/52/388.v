Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => Z.ltb x t) l.

Example test_below_threshold :
  below_threshold_spec [10000000%Z; 9000000%Z; 8000000%Z; 2000%Z; 6000000%Z; 500%Z; 2000000%Z] 15%Z false.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.