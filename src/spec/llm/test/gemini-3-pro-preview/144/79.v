Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["33/44"; "33/44"] -> x1=33, x2=44, n1=33, n2=44
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 33 44 33 44 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (33 * 33) mod (44 * 44) evaluates to 1089 *)
    (* 1089 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.