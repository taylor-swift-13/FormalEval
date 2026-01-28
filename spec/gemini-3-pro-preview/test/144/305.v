Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["333/8"; "33/8"] -> x1=333, x2=8, n1=33, n2=8
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 333 8 33 8 false.
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
    (* Simplify algebraic expressions: (333 * 33) mod (8 * 8) *)
    (* 333 * 33 = 10989 *)
    (* 8 * 8 = 64 *)
    (* 10989 mod 64 = 45 *)
    (* H_mod becomes 45 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.