Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["7/5725"; "7/725"] -> x1=7, x2=5725, n1=7, n2=725
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 7 5725 7 725 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (7 * 7) mod (5725 * 725) *)
    (* 7 * 7 = 49 *)
    (* 5725 * 725 = 4150625 *)
    (* 49 mod 4150625 = 49 *)
    (* 49 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.