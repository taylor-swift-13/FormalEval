Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["23/2"; "616/6"] -> x1=23, x2=2, n1=616, n2=6
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 23 2 616 6 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (23 * 616) mod (2 * 6) *)
    (* 23 * 616 = 14168 *)
    (* 2 * 6 = 12 *)
    (* 14168 mod 12 = 8 *)
    (* H_mod : 8 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.