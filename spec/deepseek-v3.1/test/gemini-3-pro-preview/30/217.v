Require Import List.
Require Import ZArith.
Import ListNotations.

(* Opening Z_scope is necessary to interpret negative integer literals like -1 *)
Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (result : list Z) : Prop :=
  result = filter (fun x => Z.gtb x 0) l.

Example test_get_positive:
  get_positive_spec [11; 1; 1; -8; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2] [11; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2].
Proof.
  (* Unfold the specification definition *)
  unfold get_positive_spec.
  
  (* Simplify the filter and boolean comparison operations *)
  simpl.
  
  (* Prove equality *)
  reflexivity.
Qed.