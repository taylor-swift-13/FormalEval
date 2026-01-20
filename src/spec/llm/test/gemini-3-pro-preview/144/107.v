Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["199/13"; "19/313"] -> x1=199, x2=13, n1=19, n2=313
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 199 13 19 313 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (199 * 19) mod (13 * 313) *)
    (* (199 * 19) = 3781 *)
    (* (13 * 313) = 4069 *)
    (* 3781 mod 4069 = 3781 *)
    (* H_mod becomes 3781 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate.
Qed.