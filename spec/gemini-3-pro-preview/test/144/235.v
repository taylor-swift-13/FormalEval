Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["467/7736"; "16/17"] -> x1=467, x2=7736, n1=16, n2=17
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 467 7736 16 17 false.
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
    (* Simplify algebraic expressions: (467 * 16) mod (7736 * 17) *)
    (* 467 * 16 = 7472 *)
    (* 7736 * 17 = 131512 *)
    (* 7472 mod 131512 = 7472 *)
    (* H_mod implies 7472 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.