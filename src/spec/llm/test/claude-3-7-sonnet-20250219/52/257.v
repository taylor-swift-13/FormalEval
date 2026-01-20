Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition zlist_to_natlist (l : list Z) : list nat :=
  map (fun z => if (z <? 0)%Z then 0%nat else Z.to_nat z) l.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => Nat.ltb x (if (t <? 0)%Z then 0%nat else Z.to_nat t)) (zlist_to_natlist l).

Example test_below_threshold :
  below_threshold_spec [10; 6000001; -30; 40; -50] 13 false.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.