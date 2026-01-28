Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["933/4"; "9/12"] -> x1=933, x2=4, n1=9, n2=12
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 933 4 9 12 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (933 * 9) mod (4 * 12) *)
    (* 933 * 9 = 8397 *)
    (* 4 * 12 = 48 *)
    (* 8397 mod 48 = 45 *)
    (* H_mod implies 45 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.