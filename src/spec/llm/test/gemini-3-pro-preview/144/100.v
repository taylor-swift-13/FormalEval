Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["33/34"; "3/22"] -> x1=33, x2=34, n1=3, n2=22
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 33 34 3 22 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (33 * 3) mod (34 * 22) evaluates to 99 *)
    (* 99 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.