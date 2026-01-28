Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

(* Opening R_scope is necessary to interpret real literals *)
Open Scope R_scope.

Definition get_positive_spec (l : list R) (result : list R) : Prop :=
  result = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive:
  get_positive_spec [0.5; 0; 2.5; 5; -2.2; -8; -0.75; 7.7; 9.9; -10.5] 
                    [0.5; 2.5; 5; 7.7; 9.9].
Proof.
  (* Unfold the specification definition *)
  unfold get_positive_spec.
  
  (* Simplify the filter operation *)
  simpl.
  
  (* Destruct the decision procedure for real inequalities and solve with lra *)
  repeat (destruct (Rgt_dec _ _); try lra).
  
  (* Prove equality *)
  reflexivity.
Qed.