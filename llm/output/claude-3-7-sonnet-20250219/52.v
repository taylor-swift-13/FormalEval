Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Definition below_threshold_spec (l : list nat) (t : nat) (res : bool) : Prop :=
  res = forallb (fun x => Nat.ltb x t) l.

Example test_below_threshold :
  below_threshold_spec [1; 2; 4; 10] 100 true.
Proof.
  unfold below_threshold_spec.
  simpl.
  (* Evaluate forallb (fun x => Nat.ltb x 100) [1;2;4;10] *)
  (* Nat.ltb x 100 is true for x = 1,2,4,10 *)
  reflexivity.
Qed.