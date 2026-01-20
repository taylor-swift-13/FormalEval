Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["16/17"; "3180/241"] -> x1=16, x2=17, n1=3180, n2=241
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 16 17 3180 241 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (16 * 3180) mod (17 * 241) *)
    (* 16 * 3180 = 50880 *)
    (* 17 * 241 = 4097 *)
    (* 50880 mod 4097 = 1716 *)
    (* H_mod becomes 1716 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.