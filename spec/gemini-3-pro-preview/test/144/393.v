Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["173/77"; "163/58"] -> x1=173, x2=77, n1=163, n2=58
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 173 77 163 58 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    (* Here result is false, so false = true is a contradiction *)
    intros H_contra.
    discriminate H_contra.
  - (* Right to Left: mod = 0 -> result = true *)
    (* Here result is false, so we need to show mod = 0 implies false = true (contradiction) *)
    intros H_mod.
    (* Simplify algebraic expressions: (173 * 163) mod (77 * 58) *)
    (* 173 * 163 = 28199 *)
    (* 77 * 58 = 4466 *)
    (* 28199 mod 4466 = 1403 *)
    (* H_mod becomes 1403 = 0, which is impossible *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.