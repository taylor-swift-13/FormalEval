Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import ZArith.

Definition below_threshold_spec (l : list nat) (t : nat) (res : bool) : Prop :=
  res = forallb (fun x => Nat.ltb x t) l.

(* Convert Z list to nat list with zeros for negative values *)
Fixpoint Zlist_to_natlist (l : list Z) : list nat :=
  match l with
  | [] => []
  | x :: xs => 
    let n := if Z.geb x 0 then Z.to_nat x else 0 in
    n :: Zlist_to_natlist xs
  end.

Example test_below_threshold :
  below_threshold_spec (Zlist_to_natlist [100%Z; 2000000%Z; 300%Z; (-400)%Z; 500%Z; (-600)%Z]) (Z.to_nat (-1%Z)) false.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.