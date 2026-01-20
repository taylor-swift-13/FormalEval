Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition get_positive_spec (l : list Z) (res : list Z) : Prop :=
  res = filter (fun x => Z.gtb x 0) l.

Example test_get_positive : get_positive_spec [-1; -2; 4; 5; 6] [4; 5; 6].
Proof.
  (* Unfold the definition of the specification *)
  unfold get_positive_spec.
  
  (* Simplify the expression. 
     This evaluates the filter function and the boolean comparisons (Z.gtb) 
     for the concrete integers provided in the list. *)
  simpl.
  
  (* The simplified right-hand side matches the left-hand side exactly. *)
  reflexivity.
Qed.