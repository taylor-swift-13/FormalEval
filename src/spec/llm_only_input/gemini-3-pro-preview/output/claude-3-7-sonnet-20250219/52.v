Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Definition below_threshold_spec (l : list nat) (t : nat) (res : bool) : Prop :=
  res = forallb (fun x => Nat.ltb x t) l.

Example test_below_threshold : below_threshold_spec [1; 2; 4; 10] 100 true.
Proof.
  (* Unfold the specification definition *)
  unfold below_threshold_spec.
  
  (* Simplify the boolean computation *)
  simpl.
  
  (* The goal becomes true = true, which is trivial *)
  reflexivity.
Qed.