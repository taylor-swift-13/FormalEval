Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.

Open Scope Z_scope.
Open Scope R_scope.

Inductive value : Type :=
| VInt : Z -> value
| VFloat : R -> value
| VStr : string -> value.

Parameter replace_commas_with_dots : string -> string.
Parameter R_of_string : string -> R.

Definition num_of (v : value) : R :=
  match v with
  | VInt z => IZR z
  | VFloat r => r
  | VStr s => R_of_string (replace_commas_with_dots s)
  end.

Definition compare_one_spec (a : value) (b : value) (res : option value) : Prop :=
  let ra := num_of a in
  let rb := num_of b in
  (ra = rb /\ res = None) \/
  (Rlt rb ra /\ res = Some a) \/
  (Rlt ra rb /\ res = Some b).

Example test_compare_1_2 : compare_one_spec (VInt 1) (VInt 2) (Some (VInt 2)).
Proof.
  (* Unfold the specification definition *)
  unfold compare_one_spec.
  
  (* Simplify the expression, specifically num_of *)
  simpl.
  
  (* The specification has three cases: equal, greater, less.
     We want to prove the third case (1 < 2). *)
  right. right.
  
  (* We need to prove the conjunction: IZR 1 < IZR 2 AND the result matches *)
  split.
  - (* Prove IZR 1 < IZR 2 *)
    (* Use the property that IZR preserves strict inequality *)
    apply IZR_lt.
    (* Reduce the Z inequality (1 < 2)%Z to a computation and prove it *)
    compute.
    reflexivity.
  - (* Prove Some (VInt 2) = Some (VInt 2) *)
    reflexivity.
Qed.